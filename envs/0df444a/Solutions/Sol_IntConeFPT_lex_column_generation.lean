-- Prove2me | solution 1 for IntConeFPT.lex_column_generation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:51:53.121038+00:00
-- url     : https://prove2.me/submissions/d54dcd64-51c4-4c59-9edb-611f9714770f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Definitions.Def_IntConeFPT_OracleMachine
import Theorems.Thm_IntConeFPT_oracle_substitution
import Theorems.Thm_IntConeFPT_gls_lex_oracle

open OnlineCRS.Combine IntConeFPT

private lemma iter_none {σ : Type*} (f : σ → Option σ) (h : σ) (hh : f h = none) (j : ℕ) :
    (flip bind f)^[j + 1] (some h) = none := by
  induction j with
  | zero => simpa [flip] using hh
  | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl

private lemma iter_unique {σ : Type*} (f : σ → Option σ) (a : Option σ) (h1 h2 : σ)
    (hh1 : f h1 = none) (s1 s2 : ℕ)
    (e1 : (flip bind f)^[s1] a = some h1) (e2 : (flip bind f)^[s2] a = some h2)
    (hh2 : f h2 = none) : h1 = h2 := by
  rcases le_total s1 s2 with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, Function.iterate_add_apply, e1] at e2
    cases j with
    | zero => simpa using e2
    | succ j => rw [iter_none f h1 hh1 j] at e2; exact absurd e2 (by simp)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [add_comm, Function.iterate_add_apply, e2] at e1
    cases j with
    | zero => simpa using e1.symm
    | succ j => rw [iter_none f h2 hh2 j] at e1; exact absurd e1 (by simp)

private lemma runsWithin_det {M : Machine} {x y1 y2 : List Sym} {T1 T2 : ℝ}
    (h1 : RunsWithin M x y1 T1) (h2 : RunsWithin M x y2 T2) : y1 = y2 := by
  obtain ⟨m1, -, ⟨e1⟩⟩ := h1
  obtain ⟨m2, -, ⟨e2⟩⟩ := h2
  have hs : ∀ l, M.tm.step (Turing.haltList M.tm l) = none := fun l => rfl
  have := iter_unique M.tm.step _ _ _ (hs _) _ _ e1.evals_in_steps e2.evals_in_steps (hs _)
  have h := congrArg (fun c : M.tm.Cfg => c.stk M.tm.k₁) this
  simp [Turing.haltList] at h
  exact List.map_injective_iff.2 M.outputAlphabet.symm.injective h

private lemma time_arith (C0 e K L R : ℕ) (B : ℝ) (hB : 1 ≤ B) (hL : 2 ≤ L) (hR : R ≤ L ^ K) :
    4 * (((L ^ C0 : ℕ) : ℝ) + 1) * (B * (((L ^ C0 : ℕ) : ℝ)) ^ e + ((L ^ C0 : ℕ) : ℝ) + (R : ℝ) + 4)
      ≤ B * (L : ℝ) ^ (C0 * e + 2 * C0 + K + 6) := by
  have ha : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have ha1 : (1 : ℝ) ≤ (L : ℝ) := by linarith
  have pw : ∀ i j : ℕ, i ≤ j → (L : ℝ) ^ i ≤ (L : ℝ) ^ j :=
    fun i j hij => pow_le_pow_right₀ ha1 hij
  push_cast
  set N := C0 * e + C0 + K with hN
  have hLN : (1 : ℝ) ≤ (L : ℝ) ^ N := one_le_pow₀ ha1
  have hBN : (L : ℝ) ^ N ≤ B * (L : ℝ) ^ N := le_mul_of_one_le_left (by positivity) hB
  have h1 : B * ((L : ℝ) ^ C0) ^ e ≤ B * (L : ℝ) ^ N := by
    rw [← pow_mul]; exact mul_le_mul_of_nonneg_left (pw _ _ (by omega)) (by linarith)
  have h2 : (L : ℝ) ^ C0 ≤ (L : ℝ) ^ N := pw _ _ (by omega)
  have h3 : (R : ℝ) ≤ (L : ℝ) ^ N := by
    have : (R : ℝ) ≤ (L : ℝ) ^ K := by exact_mod_cast hR
    exact this.trans (pw _ _ (by omega))
  have hsum : B * ((L : ℝ) ^ C0) ^ e + (L : ℝ) ^ C0 + (R : ℝ) + 4 ≤ 7 * (B * (L : ℝ) ^ N) := by
    nlinarith
  have ht : (L : ℝ) ^ C0 + 1 ≤ 2 * (L : ℝ) ^ C0 := by
    have : (1 : ℝ) ≤ (L : ℝ) ^ C0 := one_le_pow₀ ha1
    linarith
  have h64 : (64 : ℝ) ≤ (L : ℝ) ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 6
    norm_num at this; linarith
  have hpos : 0 ≤ B * (L : ℝ) ^ N := by positivity
  have hposC : 0 ≤ (L : ℝ) ^ C0 := by positivity
  calc 4 * ((L : ℝ) ^ C0 + 1) * (B * ((L : ℝ) ^ C0) ^ e + (L : ℝ) ^ C0 + (R : ℝ) + 4)
      ≤ 4 * (2 * (L : ℝ) ^ C0) * (7 * (B * (L : ℝ) ^ N)) := by
        apply mul_le_mul (by linarith) hsum (by positivity) (by positivity)
    _ = 56 * (B * ((L : ℝ) ^ N * (L : ℝ) ^ C0)) := by ring
    _ ≤ (L : ℝ) ^ 6 * (B * ((L : ℝ) ^ N * (L : ℝ) ^ C0)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = B * (L : ℝ) ^ (C0 * e + 2 * C0 + K + 6) := by
        rw [hN, ← pow_add, mul_left_comm, ← pow_add]
        congr 2; ring

theorem solution :
    ∀ e K : ℕ, ∃ C : ℕ, ∀ P : Machine, ∃ W : Machine,
      ∀ (d k : ℕ) (ctx : List Sym) (T A : Set (Gen d k)) (c s : (Fin d → ℝ) → ℝ) (B : ℝ),
        1 ≤ B → A ⊆ T →
        (∀ (ε : ℚ), 0 ≤ ε → ∀ (ax : Fin d → ℚ) (au : Fin k → ℚ),
          ∃ (x : Fin d → ℤ) (u : Fin k → ℚ) (cq sq : ℚ),
            ratGen x u ∈ A ∧ (cq : ℝ) = c (fun i => (x i : ℝ)) ∧
            (sq : ℝ) = s (fun i => (x i : ℝ)) ∧
            (∀ g ∈ T, (cq : ℝ) + (ε : ℝ) * sq - pairing (ratPair ax au) (ratGen x u).toReal ≤
              c (fun i => (g.1 i : ℝ)) + (ε : ℝ) * s (fun i => (g.1 i : ℝ)) -
                pairing (ratPair ax au) g.toReal) ∧
            (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length ≤ ctx.length ^ K ∧
            RunsWithin P (ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au)
              (encGen x u ++ encRat cq ++ encRat sq ++ [3])
              (B * ((ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au).length : ℝ) ^ e)) →
        ∀ (z : Fin d → ℚ) (w : Fin k → ℚ) (n : ℚ),
          ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) = 0 ∨
            (0 < (n : ℝ) ∧ ((n : ℝ)⁻¹ • (ratPair z w).1, (n : ℝ)⁻¹ • (ratPair z w).2) ∈
              convexHull ℝ (Gen.toReal '' T)) →
          let inp := encNat d ++ [3] ++ encNat k ++ [3] ++ encVec z ++ encVec w ++ encRat n ++ [3] ++ ctx
          ∃ o : ℚ × ((Fin d → ℚ) × (Fin k → ℚ)) × ℚ × List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ),
            (∀ θ : Gen d k →₀ ℝ, IsFracRep T θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
              (o.1 : ℝ) ≤ fracCost c θ) ∧
            (∀ g ∈ T, pairing (ratPair o.2.1.1 o.2.1.2) g.toReal + (o.2.2.1 : ℝ) ≤
              c (fun i => (g.1 i : ℝ))) ∧
            (o.1 : ℝ) = pairing (ratPair o.2.1.1 o.2.1.2) (ratPair z w) + (o.2.2.1 : ℝ) * n ∧
            o.2.2.2.length ≤ d + k + 1 ∧
            (o.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
            (∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ A ∧ 0 < e.2.2) ∧
            (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
            (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = n ∧
            (o.2.2.2.map fun e => (e.2.2 : ℝ) * c (fun i => (e.1 i : ℝ))).sum = o.1 ∧
            (∀ θ : Gen d k →₀ ℝ, IsFracRep T θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
              fracCost c θ ≤ o.1 →
              (o.2.2.2.map fun e => (e.2.2 : ℝ) * s (fun i => (e.1 i : ℝ))).sum ≤ fracCost s θ) ∧
            (encOracle o).length ≤ inp.length ^ C ∧
            RunsWithin W inp (encNat d ++ [3] ++ encNat k ++ [3] ++ encOracle o)
              (B * (inp.length : ℝ) ^ C) := by
  intro e K
  obtain ⟨C0, OM, hOM⟩ := gls_lex_oracle K
  refine ⟨C0 * e + 2 * C0 + K + 6, ?_⟩
  intro P
  obtain ⟨W, hW⟩ := oracle_substitution OM P
  refine ⟨W, ?_⟩
  intro d k ctx T A c s B hB hAT hprice z w n hhull inp
  classical
  -- the oracle answered by `P`
  let O : List Sym → List Sym := fun q =>
    if h : ∃ y : List Sym, ∃ T' : ℝ, RunsWithin P q y T' then Classical.choose h else []
  have hO : ∀ q y (T' : ℝ), RunsWithin P q y T' → O q = y := by
    intro q y T' hq
    have h : ∃ y : List Sym, ∃ T' : ℝ, RunsWithin P q y T' := ⟨y, T', hq⟩
    simp only [O, dif_pos h]
    obtain ⟨T'', hT''⟩ := Classical.choose_spec h
    exact runsWithin_det hT'' hq
  have hpriceO : ∀ (ε : ℚ), 0 ≤ ε → ∀ (ax : Fin d → ℚ) (au : Fin k → ℚ),
      ∃ (x : Fin d → ℤ) (u : Fin k → ℚ) (cq sq : ℚ),
        ratGen x u ∈ A ∧ (cq : ℝ) = c (fun i => (x i : ℝ)) ∧
        (sq : ℝ) = s (fun i => (x i : ℝ)) ∧
        (∀ g ∈ T, (cq : ℝ) + (ε : ℝ) * sq - pairing (ratPair ax au) (ratGen x u).toReal ≤
          c (fun i => (g.1 i : ℝ)) + (ε : ℝ) * s (fun i => (g.1 i : ℝ)) -
            pairing (ratPair ax au) g.toReal) ∧
        (encGen x u ++ encRat cq ++ encRat sq ++ [3]).length ≤ ctx.length ^ K ∧
        O (ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au) =
          encGen x u ++ encRat cq ++ encRat sq ++ [3] := by
    intro ε hε ax au
    obtain ⟨x, u, cq, sq, h1, h2, h3, h4, h5, h6⟩ := hprice ε hε ax au
    exact ⟨x, u, cq, sq, h1, h2, h3, h4, h5, hO _ _ _ h6⟩
  obtain ⟨o, hmin, hdual, hatt, hlen, hnd, hA, hagg, hcnt, hcost, hlex, henc, hrun⟩ :=
    hOM d k ctx T A c s hAT O hpriceO z w n hhull
  refine ⟨o, hmin, hdual, hatt, hlen, hnd, hA, hagg, hcnt, hcost, hlex, ?_, ?_⟩
  · calc (encOracle o).length ≤ inp.length ^ C0 := henc
      _ ≤ inp.length ^ (C0 * e + 2 * C0 + K + 6) := by
        apply Nat.pow_le_pow_right
        · have : 0 < inp.length := by simp [inp]
          omega
        · omega
  · have hctx : ctx.length ≤ inp.length := by simp only [inp, List.length_append]; omega
    have hL2 : 2 ≤ inp.length := by simp only [inp, List.length_append, List.length_singleton]; omega
    have hB0 : (0 : ℝ) ≤ B := by linarith
    have hq : ∀ q, (q.length ≤ inp.length ^ C0 ∧ ∃ (ε : ℚ) (ax : Fin d → ℚ) (au : Fin k → ℚ),
        0 ≤ ε ∧ q = ctx ++ encRat ε ++ [3] ++ encVec ax ++ encVec au) →
        q.length ≤ inp.length ^ C0 ∧ (O q).length ≤ inp.length ^ K ∧
        RunsWithin P q (O q) (B * (((inp.length ^ C0 : ℕ) : ℝ)) ^ e) := by
      rintro q ⟨hql, ε, ax, au, hε, rfl⟩
      obtain ⟨x, u, cq, sq, -, -, -, -, h5, h6⟩ := hprice ε hε ax au
      rw [hO _ _ _ h6]
      refine ⟨hql, h5.trans (Nat.pow_le_pow_left hctx _), ?_⟩
      obtain ⟨m, hm, hm'⟩ := h6
      refine ⟨m, hm.trans ?_, hm'⟩
      apply mul_le_mul_of_nonneg_left _ hB0
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast hql
    have hrunW := hW O _ inp _ (inp.length ^ C0) (inp.length ^ C0) (inp.length ^ K)
      (B * (((inp.length ^ C0 : ℕ) : ℝ)) ^ e) (by positivity) hrun hq
    obtain ⟨m, hm, hm'⟩ := hrunW
    refine ⟨m, hm.trans ?_, hm'⟩
    exact time_arith C0 e K inp.length (inp.length ^ K) B hB hL2 le_rfl
