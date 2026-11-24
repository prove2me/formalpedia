-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.APart.prod_latPt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:37.332158+00:00
-- url     : https://prove2.me/submissions/7b4293d7-eb57-4e75-9e2a-c4fa7128e557

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb


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
variable [IsTotallyReal F]
namespace GlobalTheory.HeckeTwo.APart
theorem _root_.solution (a : F) :
    ∏ τ : Emb F, latPt 0 (a, 0) τ =
      (2 * (Real.pi : ℂ) * I) ^ Fintype.card (Emb F) * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
  simp only [latPt, Pi.zero_apply, map_zero, ofReal_zero, zero_mul, add_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, prod_emb]
end GlobalTheory.HeckeTwo.APart
