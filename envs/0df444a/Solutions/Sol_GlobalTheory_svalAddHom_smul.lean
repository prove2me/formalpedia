-- Prove2me | solution 1 for GlobalTheory.svalAddHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:00.58979+00:00
-- url     : https://prove2.me/submissions/5fd84906-3d52-4fe3-8817-07a168da87a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
variable {F : Type} [CommRing F] {Z Y T : Scheme.{0}} {L : LB Z} (p : Y ⟶ Spec (CommRingCat.of F))
  {K : Type} [Fintype K] (φ : K → (Y ⟶ Z)) (ε : K → ℤ)
namespace GlobalTheory
theorem _root_.solution (r : T ⟶ Y) (z : T) {J : (T ⟶ Z) → L.ι} (hJ : Good L z J) (c : F)
    (s : SecMod p (LB.LinComb L φ ε)) :
    svalAddHom p φ ε r z hJ (c • s) =
      gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * svalAddHom p φ ε r z hJ s :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem φ r) _).trans (gs_pull r p z ⊤ trivial _)))
end GlobalTheory
