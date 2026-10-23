-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_nonconstant_has_detectable_derivative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-22T21:48:24.42909+00:00
-- url     : https://prove2.me/submissions/35bead5a-d8dd-49f7-9f82-e60aed902771
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_detectable_of_pairwise_separation_quantitative
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_separation_constant_budget
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin m → E) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ∀ F : MvPolynomial (Fin m) Complex, F ≠ 0 →
        fibreContactSupportBound (fun i => w i.succ) N F →
        (∀ word : List (Fin m),
          fibreContactWordCost (fun i => v i.succ) word ≤
            (sigma : Real) * (N : Real) →
          MvPolynomial.aeval x (fibreContactWord word F) = 0) →
        (∀ i : Fin m, ∀ a : Complex,
          x i ≠ algebraMap Complex E a) →
        ∃ word : List (Fin m),
          fibreContactWordCost (fun i => v i.succ) word ≤
            (sigma : Real) * (N : Real) ∧
          MvPolynomial.aeval x (fibreContactWord word F) ≠ 0 := by
  classical
  obtain ⟨hC, hbudget⟩ := separation_constant_budget m sigma hm hsigma
  have hpair : ∀ i j : Fin m, i < j →
      interpolationSeparationConstant m sigma * (v i.succ : Real) <
        (w j.succ : Real) := by
    intro i j hij
    have hij' : i.succ < j.succ := by
      apply Fin.lt_iff_val_lt_val.mpr
      simpa [Fin.val_succ] using (Fin.lt_iff_val_lt_val.mp hij)
    have hji : j.succ ≠ i.succ := ne_of_gt hij'
    have htail : ∀ k : Fin (m + 1), j.succ < k →
        (k ∈ ({j.succ} : Finset (Fin (m + 1))) ↔
          k ∈ ({i.succ} : Finset (Fin (m + 1)))) := by
      intro k hk
      have hkj : k ≠ j.succ := ne_of_gt hk
      have hki : k ≠ i.succ := ne_of_gt (lt_trans hij' hk)
      simp [hkj, hki]
    have h := hseparated {j.succ} {i.succ} (by simp)
      j.succ (Fin.succ_ne_zero j) (by simp) (by simpa using hji) htail
    simpa only [Finset.prod_singleton] using h
  refine ⟨0, ?_⟩
  intro N hN0 hN F hF hbound hvanish hx
  obtain ⟨word, hcost, hnonzero⟩ :=
    fibreContact_detectable_of_pairwise_separation_quantitative
      (interpolationSeparationConstant m sigma) hC
      (fun i => w i.succ) (fun i => v i.succ)
      (fun i => hw i.succ) (fun i => hv i.succ) hpair E x hx N hN F hF hbound
  exact ⟨word, hcost.trans
    (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N)), hnonzero⟩
