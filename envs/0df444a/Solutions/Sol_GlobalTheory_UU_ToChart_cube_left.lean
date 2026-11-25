-- Prove2me | solution 1 for GlobalTheory.UU.ToChart.cube_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:55:35.103031+00:00
-- url     : https://prove2.me/submissions/63ae3957-a11e-4fac-a3a0-e4e8a1c395aa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ToChart
namespace GlobalTheory.UU.ToChart
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {T : Over S} {T' : Over S'} (β : (T' ⟶ G') →* (T ⟶ G)) (x : Fin 3 → (T' ⟶ G')) (k : thK) :
    (lift (β (x 0)) (lift (β (x 1)) (β (x 2)))).left ≫ thφ G (x3 G) k = (β (psum G' x k.down)).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift (β (x 0)) (lift (β (x 1)) (β (x 2))))) (x3 G) k.down).trans
    ((congrArg (fun q => psum G q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])).trans
      (psum_hom β x k.down).symm))
end GlobalTheory.UU.ToChart
