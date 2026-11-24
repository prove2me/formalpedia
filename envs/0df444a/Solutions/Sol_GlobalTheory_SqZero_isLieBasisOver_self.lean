-- Prove2me | solution 1 for GlobalTheory.SqZero.isLieBasisOver_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:54:08.938911+00:00
-- url     : https://prove2.me/submissions/4672716c-f097-485b-8442-1a81f9fc4e9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Theorems.Thm_GlobalTheory_SqZero_isTanOver_tanExp
import Theorems.Thm_GlobalTheory_SqZero_isLieComb_iff_lieExp
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {S S' A : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing A] [Algebra R A]
variable {v : Fin n → (epsR R ⟶ G)}
namespace GlobalTheory.SqZero
theorem _root_.solution (hv : IsLieBasis v) : IsLieBasisOver R v := by
  refine ⟨fun s s' h => ?_, fun w hw => ?_⟩
  · exact (hv.2 _ ((isTan_iff _).1 (isTanOver_tanExp hv.1 s))).unique
      ((isLieComb_iff_lieExp _ _).2 rfl) ((isLieComb_iff_lieExp _ _).2 h)
  · obtain ⟨c, hc, -⟩ := hv.2 w ((isTan_iff _).1 hw)
    exact ⟨c, (isLieComb_iff_lieExp _ _).1 hc⟩
end GlobalTheory.SqZero
