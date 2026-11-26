-- Prove2me | solution 1 for IntConeFPT.lemma_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:25:59.252538+00:00
-- url     : https://prove2.me/submissions/04a0ddb9-d7fb-4e22-8f46-903637213eaf
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
import Definitions.Def_IntConeFPT_fracMerge
import Theorems.Thm_IntConeFPT_runsWithin_chain
import Theorems.Thm_IntConeFPT_lemma_5_lex_lp
import Theorems.Thm_IntConeFPT_lemma_5_merge_writer
import Theorems.Thm_IntConeFPT_lemma_5_merge_support

open OnlineCRS.Combine IntConeFPT

private lemma time_arith (C1 C2 d A Y : ℕ) (hA2 : 2 ≤ A) (hyA : Y ≤ A ^ (C1 + 2)) :
    oracleBound C1 d A + (Y : ℝ) ^ C2 + 2 * ((Y : ℝ) + 1) ≤
      oracleBound (C1 + (C1 + 2) * C2 + (C1 + 2) + 3) d A := by
  have ha : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  have ha1 : (1 : ℝ) ≤ (A : ℝ) := by linarith
  have hlog : 0 ≤ (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1) := by
    apply mul_nonneg (by positivity)
    apply Real.logb_nonneg (by norm_num)
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  set E1 : ℝ := (2 : ℝ) ^ ((C1 : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) with hE1
  set E : ℝ := (2 : ℝ) ^ (((C1 + (C1 + 2) * C2 + (C1 + 2) + 3 : ℕ) : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) with hE
  have hE1E : E1 ≤ E := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hlog
    exact_mod_cast (show C1 ≤ C1 + (C1 + 2) * C2 + (C1 + 2) + 3 by omega)
  have hE1pos : 1 ≤ E1 := Real.one_le_rpow (by norm_num) (by
    rw [mul_assoc]; exact mul_nonneg (by positivity) hlog)
  have hE1' : 1 ≤ E := hE1pos.trans hE1E
  have pw : ∀ i j : ℕ, i ≤ j → (A : ℝ) ^ i ≤ (A : ℝ) ^ j :=
    fun i j hij => pow_le_pow_right₀ ha1 hij
  have hyR : (Y : ℝ) ≤ (A : ℝ) ^ (C1 + 2) := by exact_mod_cast hyA
  have hT1 : oracleBound C1 d A ≤ E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := by
    unfold oracleBound
    rw [← hE1]
    exact mul_le_mul hE1E (pw _ _ (le_add_left (by omega))) (by positivity) (by linarith)
  have hT2 : (Y : ℝ) ^ C2 ≤ E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := by
    calc (Y : ℝ) ^ C2 ≤ ((A : ℝ) ^ (C1 + 2)) ^ C2 :=
          pow_le_pow_left₀ (by positivity) hyR _
      _ = (A : ℝ) ^ ((C1 + 2) * C2) := (pow_mul _ _ _).symm
      _ ≤ (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := pw _ _ (by omega)
      _ ≤ E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := le_mul_of_one_le_left (by positivity) hE1'
  have hT3 : 2 * ((Y : ℝ) + 1) ≤ 4 * (E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2))) := by
    have h1 : (A : ℝ) ^ (C1 + 2) ≤ (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := pw _ _ (by omega)
    have h2 : (1 : ℝ) ≤ (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := one_le_pow₀ ha1
    have h3 : (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) ≤ E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := le_mul_of_one_le_left (by positivity) hE1'
    linarith
  have h8 : (6 : ℝ) ≤ (A : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 3
    norm_num at this; linarith
  have hT1' := hT1
  unfold oracleBound at hT1' ⊢
  rw [← hE1] at hT1' ⊢
  rw [← hE]
  have hpw : (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2) + 3) ≤
      (A : ℝ) ^ (C1 + (C1 + 2) * C2 + (C1 + 2) + 3) := pw _ _ (by omega)
  have hEN : 0 ≤ E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2)) := by positivity
  calc _ ≤ 6 * (E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2))) := by linarith
    _ ≤ (A : ℝ) ^ 3 * (E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2))) :=
        mul_le_mul_of_nonneg_right h8 hEN
    _ = E * (A : ℝ) ^ ((C1 + 2) * C2 + (C1 + 2) + 3) := by ring
    _ ≤ E * (A : ℝ) ^ (C1 + (C1 + 2) * C2 + (C1 + 2) + 3) :=
        mul_le_mul_of_nonneg_left hpw (by positivity)

theorem solution :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℚ) (w : Fin I.k → ℚ) (n : ℚ),
        (I.Sr t r).Nonempty →
        ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∈ I.Cr t r →
        let inp := encLocal I t r ++ encVec z ++ encVec w ++ encRat n ++ [3]
        ∃ o : ℚ × ((Fin I.d → ℚ) × (Fin I.k → ℚ)) × ℚ × List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ),
          ((o.1 : ℝ) : EReal) = I.Phi t r ((ratPair z w).1, (ratPair z w).2, (n : ℝ)) ∧
          (ratPair o.2.1.1 o.2.1.2, (o.2.2.1 : ℝ)) ∈ I.Dr t r ∧
          (o.1 : ℝ) = pairing (ratPair o.2.1.1 o.2.1.2) (ratPair z w) + (o.2.2.1 : ℝ) * n ∧
          o.2.2.2.length ≤ min (2 ^ I.d) (I.d + I.k + 1) ∧
          (o.2.2.2.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2) ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum = ratPair z w ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = n ∧
          (o.2.2.2.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = o.1 ∧
          (encOracle o).length ≤ inp.length ^ C ∧
          RunsWithin M inp (encOracle o) (oracleBound C I.d inp.length) := by
  obtain ⟨C1, M1, h1⟩ := lemma_5_lex_lp
  obtain ⟨C2, M2, h2⟩ := lemma_5_merge_writer
  obtain ⟨W, hW⟩ := runsWithin_chain M1 M2
  refine ⟨C1 + (C1 + 2) * C2 + (C1 + 2) + 3, W, ?_⟩
  intro I hI t r z w n hne hC inp
  obtain ⟨o, hφ, hD, hatt, hlen, hnd, hV, hagg, hcnt, hcost, hlex, henc, hrun⟩ :=
    h1 I hI t r z w n hne hC
  have hS : ∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2 :=
    fun e he => ⟨(hV e he).1.1, (hV e he).2⟩
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ :=
    lemma_5_merge_support I hI t r z w n o.1 o.2.2.2 hS hagg hcnt hcost hlex
  obtain ⟨hout, hrun2⟩ := h2 I.d I.k o (fun e he => (hS e he).2)
  -- lengths
  set pre : List Sym := encNat I.d ++ [3] ++ encNat I.k ++ [3] with hpre
  set A : ℕ := inp.length with hA
  have hpreA : pre.length ≤ A := by
    simp only [hA, inp, hpre, encLocal, encInstance, List.length_append]
    omega
  have hpre2 : 2 ≤ pre.length := by simp [hpre]; omega
  have hA2 : 2 ≤ A := le_trans hpre2 hpreA
  have hA1 : 1 ≤ A := by omega
  set y : List Sym := pre ++ encOracle o with hy
  have hyA : y.length ≤ A ^ (C1 + 2) := by
    have e1 : A ≤ A ^ (C1 + 1) := by
      calc A = A ^ 1 := (pow_one A).symm
        _ ≤ A ^ (C1 + 1) := Nat.pow_le_pow_right hA1 (by omega)
    have e2 : A ^ C1 ≤ A ^ (C1 + 1) := Nat.pow_le_pow_right hA1 (by omega)
    have e3 : 2 * A ^ (C1 + 1) ≤ A ^ (C1 + 2) := by
      rw [pow_succ A (C1 + 1)]
      calc 2 * A ^ (C1 + 1) = A ^ (C1 + 1) * 2 := by ring
        _ ≤ A ^ (C1 + 1) * A := Nat.mul_le_mul_left _ hA2
    simp only [hy, List.length_append]
    omega
  have hout' : (encOracle (o.1, o.2.1, o.2.2.1, fracMerge o.2.2.2)).length ≤
      A ^ (C1 + (C1 + 2) * C2 + (C1 + 2) + 3) := by
    calc _ ≤ y.length ^ C2 := hout
      _ ≤ (A ^ (C1 + 2)) ^ C2 := Nat.pow_le_pow_left hyA _
      _ = A ^ ((C1 + 2) * C2) := (pow_mul A (C1 + 2) C2).symm
      _ ≤ A ^ (C1 + (C1 + 2) * C2 + (C1 + 2) + 3) := Nat.pow_le_pow_right hA1 (by linarith)
  refine ⟨(o.1, o.2.1, o.2.2.1, fracMerge o.2.2.2), hφ, hD, hatt,
    le_min m1 (m2.trans hlen), m3, m4, m5, m6, m7, hout', ?_⟩
  have hrun3 := hW inp y _ _ _ hrun hrun2
  obtain ⟨m, hm, hm'⟩ := hrun3
  refine ⟨m, le_trans hm ?_, hm'⟩
  exact time_arith C1 C2 I.d A y.length hA2 hyA
