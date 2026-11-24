-- Prove2me | solution 1 for GlobalTheory.HeckeLat.periodic_bound_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:53:55.9479+00:00
-- url     : https://prove2.me/submissions/1305d146-1d0d-4fac-b46c-c0ba08f836fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType
import Theorems.Thm_GlobalTheory_HeckeLat_one_le_norm_emb
import Theorems.Thm_GlobalTheory_HeckeLat_summable_exp_emb
import Theorems.Thm_GlobalTheory_HeckeLat_bounded_of_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeLat
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeLat
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  intro K _ _ _ I _ φ hφ M F hM hF
  obtain ⟨C, hC⟩ := bounded_of_periodic F hM hF
  refine ⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩
  refine ((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  exact mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le
end GlobalTheory.HeckeLat
