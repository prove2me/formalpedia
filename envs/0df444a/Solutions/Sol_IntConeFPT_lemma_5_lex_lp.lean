-- Prove2me | solution 1 for IntConeFPT.lemma_5_lex_lp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:42:38.997569+00:00
-- url     : https://prove2.me/submissions/58fb2deb-4546-4ea9-a878-cf8ece282347
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
import Theorems.Thm_IntConeFPT_runsWithin_chain
import Theorems.Thm_IntConeFPT_lex_column_generation
import Theorems.Thm_IntConeFPT_lemma_5_pricer
import Theorems.Thm_IntConeFPT_lemma_5_lex_lp_prep_writer

open OnlineCRS.Combine IntConeFPT

/-- The finitely supported function of a weighted generator list. -/
private noncomputable def listRep {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    Gen d k →₀ ℝ :=
  (L.map fun e => Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ)).sum

private lemma listRep_sum {d k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : Gen d k → ℝ → M) (h0 : ∀ g, F g 0 = 0) (hadd : ∀ g a b, F g (a + b) = F g a + F g b)
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    (listRep L).sum F = (L.map fun e => F (ratGen e.1 e.2.1) (e.2.2 : ℝ)).sum := by
  induction L with
  | nil => simp [listRep]
  | cons e L ih =>
    have : listRep (e :: L) = Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ) + listRep L := by
      simp [listRep]
    rw [this, Finsupp.sum_add_index' h0 hadd, Finsupp.sum_single_index (h0 _), ih]
    simp

private lemma listRep_support {d k : ℕ} (S : Set (Gen d k))
    (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) (hL : ∀ e ∈ L, ratGen e.1 e.2.1 ∈ S) :
    (↑(listRep L).support : Set (Gen d k)) ⊆ S := by
  classical
  induction L with
  | nil => simp [listRep]
  | cons e L ih =>
    have : listRep (e :: L) = Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ) + listRep L := by
      simp [listRep]
    rw [this]
    intro g hg
    have hg' := Finsupp.support_add hg
    rcases Finset.mem_union.1 hg' with h | h
    · have := Finsupp.support_single_subset h
      rw [Finset.mem_singleton] at this
      rw [this]; exact hL e (by simp)
    · exact ih (fun e' he' => hL e' (by simp [he'])) h

private lemma listRep_nonneg {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ))
    (hL : ∀ e ∈ L, 0 < e.2.2) (g : Gen d k) : 0 ≤ listRep L g := by
  induction L with
  | nil => simp [listRep]
  | cons e L ih =>
    have : listRep (e :: L) = Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ) + listRep L := by
      simp [listRep]
    rw [this, Finsupp.add_apply]
    have h1 : 0 ≤ Finsupp.single (ratGen e.1 e.2.1) (e.2.2 : ℝ) g := by
      rw [Finsupp.single_apply]
      split_ifs
      · exact_mod_cast (hL e (by simp)).le
      · exact le_refl _
    exact add_nonneg h1 (ih (fun e' he' => hL e' (by simp [he'])))

private lemma two_le_rpow_one {C d : ℕ} :
    1 ≤ (2 : ℝ) ^ ((C : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) := by
  apply Real.one_le_rpow (by norm_num)
  apply mul_nonneg (mul_nonneg (by positivity) (by positivity))
  apply Real.logb_nonneg (by norm_num)
  have : (0 : ℝ) ≤ d := by positivity
  linarith

private lemma rpow_mono {C C' d : ℕ} (h : C ≤ C') :
    (2 : ℝ) ^ ((C : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) ≤
      (2 : ℝ) ^ ((C' : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hlog : 0 ≤ (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1) := by
    apply mul_nonneg (by positivity)
    apply Real.logb_nonneg (by norm_num)
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hlog

private lemma time_arith (Cp C1 Cg d L M : ℕ) (hL : 2 ≤ L) (hM : M ≤ 2 * L) :
    ((L : ℝ) + 2) ^ C1 +
        (2 : ℝ) ^ ((Cp : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) * (M : ℝ) ^ Cg +
        2 * ((M : ℝ) + 1) ≤
      oracleBound (Cp + 2 * C1 + 2 * Cg + 5) d L := by
  unfold oracleBound
  set B := (2 : ℝ) ^ ((Cp : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) with hB
  set E := (2 : ℝ) ^ (((Cp + 2 * C1 + 2 * Cg + 5 : ℕ) : ℝ) * (d : ℝ) ^ 2 *
    Real.logb 2 ((d : ℝ) + 1)) with hE
  have hB1 : 1 ≤ B := two_le_rpow_one
  have hBE : B ≤ E := rpow_mono (by omega)
  have hE1 : 1 ≤ E := hB1.trans hBE
  have ha : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have ha1 : (1 : ℝ) ≤ (L : ℝ) := by linarith
  have pw : ∀ i j : ℕ, i ≤ j → (L : ℝ) ^ i ≤ (L : ℝ) ^ j :=
    fun i j hij => pow_le_pow_right₀ ha1 hij
  have hsq : (L : ℝ) + 2 ≤ (L : ℝ) ^ 2 := by nlinarith
  have hMR : (M : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (M : ℝ) ≤ 2 * L := by exact_mod_cast hM
    nlinarith
  set N := 2 * C1 + 2 * Cg + 2 with hN
  have hLN : (1 : ℝ) ≤ (L : ℝ) ^ N := one_le_pow₀ ha1
  have hEN : 0 ≤ E * (L : ℝ) ^ N := by positivity
  have h1 : ((L : ℝ) + 2) ^ C1 ≤ E * (L : ℝ) ^ N := by
    calc ((L : ℝ) + 2) ^ C1 ≤ ((L : ℝ) ^ 2) ^ C1 := pow_le_pow_left₀ (by positivity) hsq _
      _ = (L : ℝ) ^ (2 * C1) := (pow_mul _ _ _).symm
      _ ≤ (L : ℝ) ^ N := pw _ _ (by omega)
      _ ≤ E * (L : ℝ) ^ N := le_mul_of_one_le_left (by positivity) hE1
  have h2 : B * (M : ℝ) ^ Cg ≤ E * (L : ℝ) ^ N := by
    apply mul_le_mul hBE _ (by positivity) (by positivity)
    calc (M : ℝ) ^ Cg ≤ ((L : ℝ) ^ 2) ^ Cg := pow_le_pow_left₀ (by positivity) hMR _
      _ = (L : ℝ) ^ (2 * Cg) := (pow_mul _ _ _).symm
      _ ≤ (L : ℝ) ^ N := pw _ _ (by omega)
  have h3 : 2 * ((M : ℝ) + 1) ≤ 4 * (E * (L : ℝ) ^ N) := by
    have : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ N := pw _ _ (by omega)
    have : (L : ℝ) ^ N ≤ E * (L : ℝ) ^ N := le_mul_of_one_le_left (by positivity) hE1
    linarith
  have h8 : (6 : ℝ) ≤ (L : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 3
    norm_num at this; linarith
  have hpw : (L : ℝ) ^ (N + 3) ≤ (L : ℝ) ^ (Cp + 2 * C1 + 2 * Cg + 5) := pw _ _ (by omega)
  calc _ ≤ 6 * (E * (L : ℝ) ^ N) := by linarith
    _ ≤ (L : ℝ) ^ 3 * (E * (L : ℝ) ^ N) := mul_le_mul_of_nonneg_right h8 hEN
    _ = E * (L : ℝ) ^ (N + 3) := by ring
    _ ≤ E * (L : ℝ) ^ (Cp + 2 * C1 + 2 * Cg + 5) := mul_le_mul_of_nonneg_left hpw (by positivity)

theorem solution :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n : ℚ),
        (I.Sr t r).Nonempty →
        ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∈ I.Cr t r →
        let inp := encLocal I t r ++ encVec z ++ encVec w ++ encRat n ++ [3]
        let p : (Fin I.d → ℝ) → ℝ := fun x => ∑ i, ((x i - ((r i : ℕ) : ℝ)) / 2 ^ I.d) ^ 2
        ∃ o : ℚ × ((Fin I.d → ℚ) × (Fin I.k → ℚ)) × ℚ × List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ),
          ((o.1 : ℝ) : EReal) = I.Phi t r ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∧
          (ratPair o.2.1.1 o.2.1.2, (o.2.2.1 : ℝ)) ∈ I.Dr t r ∧
          (o.1 : ℝ) = pairing (ratPair o.2.1.1 o.2.1.2) (ratPair z w) + (o.2.2.1 : ℝ) * n ∧
          o.2.2.2.length ≤ I.d + I.k + 1 ∧
          (o.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ I.Vr t r ∧ 0 < e.2.2) ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = n ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = o.1 ∧
          (∀ θ : Gen I.d I.k →₀ ℝ,
            IsFracRep (I.Sr t r) θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) →
            fracCost (I.f t) θ ≤ o.1 →
            (o.2.2.2.map fun e => (e.2.2 : ℝ) * p (fun i => (e.1 i : ℝ))).sum ≤ fracCost p θ) ∧
          (encOracle o).length ≤ inp.length ^ C ∧
          RunsWithin M inp (encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encOracle o)
            (oracleBound C I.d inp.length) := by
  obtain ⟨Cp, P, hP⟩ := lemma_5_pricer
  obtain ⟨C1, F, hF⟩ := lemma_5_lex_lp_prep_writer
  obtain ⟨Cg, hG⟩ := lex_column_generation Cp Cp
  obtain ⟨W, hW⟩ := hG P
  obtain ⟨V, hV⟩ := runsWithin_chain F W
  refine ⟨Cp + 2 * C1 + 2 * Cg + 5, V, ?_⟩
  intro I hI t r z w n hne hC inp p
  set B : ℝ := (2 : ℝ) ^ ((Cp : ℝ) * (I.d : ℝ) ^ 2 * Real.logb 2 ((I.d : ℝ) + 1)) with hB
  have hB1 : 1 ≤ B := two_le_rpow_one
  have hVS : I.Vr t r ⊆ I.Sr t r := fun g hg => hg.1
  have hprice := fun (ε : ℚ) (hε : 0 ≤ ε) (ax : Fin I.d → ℚ) (au : Fin I.k → ℚ) =>
    hP I hI t r hne ε hε ax au
  obtain ⟨o, hmin, hdual, hatt, hlen, hnd, hA, hagg, hcnt, hcost, hlex, henc, hrun⟩ :=
    hW I.d I.k (encLocal I t r) (I.Sr t r) (I.Vr t r) (I.f t) p B hB1 hVS
      (fun ε hε ax au => hprice ε hε ax au) z w n hC
  have hrunF := hF I hI t r z w n
  -- lengths
  set pre : List Sym := encNat I.d ++ [3] ++ encNat I.k ++ [3] with hpre
  set mid : List Sym := encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encVec z ++ encVec w ++
    encRat n ++ [3] ++ encLocal I t r with hmid
  have hpreL : pre.length ≤ (encLocal I t r).length := by
    simp only [hpre, encLocal, encInstance, List.length_append]
    omega
  have hmidL : mid.length ≤ 2 * inp.length := by
    simp only [hmid, inp, List.length_append] at hpreL ⊢
    simp only [hpre, List.length_append] at hpreL
    omega
  have hL2 : 2 ≤ inp.length := by
    have : 2 ≤ pre.length := by simp [hpre]; omega
    have h' : (encLocal I t r).length ≤ inp.length := by
      simp only [inp, List.length_append]; omega
    omega
  refine ⟨o, ?_, fun g hg => hdual g (hVS hg), hatt, hlen, hnd, hA, hagg, hcnt, hcost, hlex,
    ?_, ?_⟩
  · -- the value is Φ
    unfold Instance.Phi
    apply le_antisymm
    · refine le_iInf₂ fun θ hθ => ?_
      exact EReal.coe_le_coe_iff.2 (hmin θ ⟨hθ.1.trans hVS, hθ.2⟩)
    · have hrep : IsFracRep (I.Vr t r) (listRep o.2.2.2)
          ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) := by
        refine ⟨listRep_support _ _ (fun e he => (hA e he).1),
          listRep_nonneg _ (fun e he => (hA e he).2), ?_, ?_⟩
        · rw [listRep_sum (fun g c => c • g.toReal) (fun g => zero_smul _ _)
            (fun g a b => add_smul a b _)]
          exact hagg
        · rw [listRep_sum (fun _ c => c) (fun _ => rfl) (fun _ _ _ => rfl)]
          exact hcnt
      have hc : fracCost (I.f t) (listRep o.2.2.2) = o.1 := by
        unfold fracCost
        rw [listRep_sum (fun g c => c * I.f t (fun i => (g.1 i : ℝ))) (fun g => zero_mul _)
          (fun g a b => add_mul a b _)]
        exact hcost
      calc (⨅ θ ∈ {θ | IsFracRep (I.Vr t r) θ ((ratPair z w).1, (ratPair z w).2, (n : ℝ))},
            ((fracCost (I.f t) θ : ℝ) : EReal)) ≤ ((fracCost (I.f t) (listRep o.2.2.2) : ℝ) : EReal) :=
            iInf₂_le (listRep o.2.2.2) hrep
        _ = ((o.1 : ℝ) : EReal) := by rw [hc]
  · calc (encOracle o).length ≤ mid.length ^ Cg := henc
      _ ≤ (2 * inp.length) ^ Cg := Nat.pow_le_pow_left hmidL _
      _ ≤ (inp.length ^ 2) ^ Cg := Nat.pow_le_pow_left (by rw [sq]; exact Nat.mul_le_mul_right _ hL2) _
      _ = inp.length ^ (2 * Cg) := (pow_mul _ _ _).symm
      _ ≤ inp.length ^ (Cp + 2 * C1 + 2 * Cg + 5) := Nat.pow_le_pow_right (by omega) (by omega)
  · obtain ⟨m, hm, hm'⟩ := hV inp mid _ _ _ hrunF hrun
    refine ⟨m, le_trans hm ?_, hm'⟩
    exact time_arith Cp C1 Cg I.d inp.length mid.length hL2 hmidL
