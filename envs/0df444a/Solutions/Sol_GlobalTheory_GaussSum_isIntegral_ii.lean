-- Prove2me | solution 1 for GlobalTheory.GaussSum.isIntegral_ii
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:11.737794+00:00
-- url     : https://prove2.me/submissions/bb624d8d-8867-4091-9d23-6655286da194

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableGaussianExtensionNormRpow
import Theorems.Thm_GlobalTheory_GaussExt_ii_sq


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
open GlobalTheory GlobalTheory.GaussSum
open GlobalTheory.GaussExt
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.GaussSum
theorem _root_.solution : IsIntegral ℤ (ii F) :=
  ⟨X ^ 2 + 1, by monicity!, by simp [ii_sq]⟩
end GlobalTheory.GaussSum
