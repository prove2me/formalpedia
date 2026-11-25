-- Prove2me | solution 1 for GlobalTheory.GaussSum.summable_gauss_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:33:29.757484+00:00
-- url     : https://prove2.me/submissions/0df10e2d-2846-40b5-9061-ece3b450f108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableGaussianExtensionNormRpow
import Theorems.Thm_GlobalTheory_GaussSum_summable_norm_rpow
import Theorems.Thm_GlobalTheory_HeckeTwo_APart_summable_norm_rpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.GaussSum
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  intro F _ _ _ 𝔞 𝔟 t ht hQ
  exact GlobalTheory.GaussSum.summable_norm_rpow 𝔞 𝔟 ht hQ
end GlobalTheory.GaussSum
