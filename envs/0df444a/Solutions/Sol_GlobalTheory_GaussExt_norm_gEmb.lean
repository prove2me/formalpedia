-- Prove2me | solution 1 for GlobalTheory.GaussExt.norm_gEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:53:53.629356+00:00
-- url     : https://prove2.me/submissions/8a40c816-6ebb-4d3a-987e-36402acd2b04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPair
import Theorems.Thm_GlobalTheory_GaussExt_norm_gEmb_F
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb


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
open GlobalTheory GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.GaussExt
theorem _root_.solution (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp
end GlobalTheory.GaussExt
