-- Prove2me | solution 1 for GlobalTheory.tauBal_of_isPullDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:57:18.350205+00:00
-- url     : https://prove2.me/submissions/753b6ff2-2a92-4c01-abf4-ae99d3e7cc73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauBalPull_tauBal_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A), IsMonHom f → IsMonHom g → RosatiAdj D.P.A D.P.L f g → f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f → g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g → ∀ (a b : D.X → D.X) (a' b' : D'.X → D'.X), (∀ y, hD.xe (a' y) = a (hD.xe y)) → (∀ y, hD.xe (b' y) = b (hD.xe y)) → (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → D.TauBal f g a b → D'.TauBal f' g' a' b' :=
  fun hG _ _ _ _ _ _ _ _ _ hD _ _ _ _ _ _ hr hf hg _ _ _ _ ha hb ca cb hB =>
    TauBalPull.tauBal_pull hG hD hr hf hg ha hb ca cb hB
end GlobalTheory
