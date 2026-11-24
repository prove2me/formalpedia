-- Prove2me | solution 1 for GlobalTheory.HeckeLat.bounded_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:50.178129+00:00
-- url     : https://prove2.me/submissions/d72a81e7-238e-4ae1-91f3-98756ee45762

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmType

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
theorem _root_.solution {M : Ideal (𝓞 K)} (F : 𝓞 K → ℂ) (hM : M ≠ ⊥)
    (hF : ∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) : ∃ C : ℝ, ∀ α, ‖F α‖ ≤ C := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM
  haveI := Fintype.ofFinite (𝓞 K ⧸ M)
  refine ⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩
  have hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have hα : F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
    have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem
    rwa [add_sub_cancel] at this
  rw [hα]
  exact Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)
end GlobalTheory.HeckeLat
