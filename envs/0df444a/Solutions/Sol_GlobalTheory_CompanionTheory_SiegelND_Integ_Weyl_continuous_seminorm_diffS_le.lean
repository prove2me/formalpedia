-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.continuous_seminorm_diffS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:38.248191+00:00
-- url     : https://prove2.me/submissions/72a1a32d-05c9-414d-aa9d-8e52aa5a4641

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_seminorm_diffS_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
theorem _root_.solution (f : SchwartzMap V ℂ) (K : ℕ)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V, p (diffS f y) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) p hp
  choose D hD0 hD using fun m : ℕ × ℕ => seminorm_diffS_le f m.1 m.2 K
  refine ⟨C * ∑ m ∈ s, D m, mul_nonneg C.2 (Finset.sum_nonneg fun m _ => hD0 m), fun y => ?_⟩
  have hw : 0 ≤ ((1 + ‖y‖) ^ K)⁻¹ := by positivity
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) ≤
      (∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹ := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun m _ => hD0 m) hw) fun m hm => ?_
    refine (hD m y).trans (mul_le_mul_of_nonneg_right ?_ hw)
    exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) hm
  calc p (diffS f y) ≤ (C • s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) := hC _
    _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (diffS f y) := rfl
    _ ≤ (C : ℝ) * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) :=
        mul_le_mul_of_nonneg_left hsup C.2
    _ = _ := by ring
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
