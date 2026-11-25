-- Prove2me | solution 1 for GlobalTheory.HodgeTateCompare.dualBC_tangentPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:49:50.308804+00:00
-- url     : https://prove2.me/submissions/908b5276-a9ed-4efb-a0e3-4dd7fd73e071

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_HodgeTateImage_dualBC_fst
import Theorems.Thm_GlobalTheory_HodgeTateImage_dualBC_snd
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateCompare
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
noncomputable section
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
namespace GlobalTheory.HodgeTateCompare
theorem _root_.solution {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (v : Cotangent G →ₗ[O] R) :
    ptMap (dualBC φ) ≫ (tangentPt v : specO O (DualNumber R) ⟶ G) =
      tangentPt (φ.toLinearMap ∘ₗ v) := by
  rw [tangentPt_eq, tangentPt_eq, ← Category.assoc, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun b => TrivSqZeroExt.ext ?_ ?_
  · simp [dualBC_fst, tangentAlg_fst]
  · simp [dualBC_snd, tangentAlg_snd]
end GlobalTheory.HodgeTateCompare
