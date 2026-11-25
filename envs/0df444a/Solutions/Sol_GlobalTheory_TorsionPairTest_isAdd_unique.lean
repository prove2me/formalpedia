-- Prove2me | solution 1 for GlobalTheory.TorsionPairTest.isAdd_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:11.528514+00:00
-- url     : https://prove2.me/submissions/0414bf10-d4dd-4fb4-a6a4-a476b4a0c00f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty
import Theorems.Thm_GlobalTheory_TorsionPairTest_ext_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
namespace GlobalTheory.TorsionPairTest
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} {g g' a a' : GtPt D T} (h : g.IsAdd g' a)
    (h' : g.IsAdd g' a') : a = a' :=
  ext_val (h.1.trans h'.1.symm) fun χ y J hJ => by
    have e := (Geo.Tor.val_corr hJ (h.2 χ) (𝟙 _)).trans (Geo.Tor.val_corr hJ (h'.2 χ) (𝟙 _)).symm
    exact mul_right_cancel ((Geo.Tor.val_mul hJ _ _ _).symm.trans (e.trans (Geo.Tor.val_mul hJ _ _ _)))
end GlobalTheory.TorsionPairTest
