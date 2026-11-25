-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.isPullF_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:41:19.732241+00:00
-- url     : https://prove2.me/submissions/b30d5e86-e134-411b-b591-61c6be762f64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution (σ : TF (R := R) F ⟶ T) (g : GtPt D T) (g' : GtPtF D F) :
    GtPt.IsPullF F σ.left g g' ↔ g'.b = σ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) σ.left y J :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩ (forall_congr' fun _ =>
    ⟨fun h _ _ hJ => (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])),
     fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans
      ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm⟩)
end GlobalTheory.FieldRestrictionTest
