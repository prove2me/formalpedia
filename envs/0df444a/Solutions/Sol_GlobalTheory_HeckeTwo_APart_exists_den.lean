-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.APart.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:29.096956+00:00
-- url     : https://prove2.me/submissions/9ab7c972-ba9e-471e-ba98-536499903086

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.APart
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwo.APart
theorem _root_.solution (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ b ∈ I, ∃ x : 𝓞 F, (x : F) = (d : F) * b := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun b hb => ?_⟩
  obtain ⟨x, hx⟩ := h b hb
  exact ⟨x, by rw [← Algebra.smul_def] at *; simpa using hx⟩
end GlobalTheory.HeckeTwo.APart
