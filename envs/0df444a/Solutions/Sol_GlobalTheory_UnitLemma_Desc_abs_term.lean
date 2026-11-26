-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.abs_term
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:36:12.379124+00:00
-- url     : https://prove2.me/submissions/6c805602-4a1b-42ab-a455-433be5902637

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology Classical
variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem solution (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  have hbound (J : Finset ι) (f : B.A → ℚ) (hf : ∀ y, |f y| ≤ 1) (y : B.A) :
      |dlt π J f y| ≤ (2 : ℚ) ^ J.card := by
    rw [dlt]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have htermbound : ∀ K ∈ J.powerset, |(-1 : ℚ) ^ K.card * f ((∏ j ∈ K, π j) * y)| ≤ 1 := by
      intro K hK
      rw [abs_mul, abs_neg_one_pow, one_mul]
      exact hf _
    refine (Finset.sum_le_card_nsmul _ _ 1 htermbound).trans ?_
    simp [nsmul_eq_mul, Finset.card_powerset]
  have hM : ∀ y, |indM B M y| ≤ 1 := by
    intro y
    simp only [indM]
    split_ifs <;> simp
  have hD : ∀ y, |indD B M y| ≤ 1 := by
    intro y
    simp only [indD]
    split_ifs <;> simp
  rw [term, abs_mul]
  exact mul_le_mul (hbound I (indM B M) hM u) (hbound I' (indD B M) hD s)
    (abs_nonneg _) (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)
