-- Prove2me | solution 1 for GlobalTheory.UU.UnitCob.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:52:39.777166+00:00
-- url     : https://prove2.me/submissions/baf53d78-8d05-491f-9d0a-9dac68da7a36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory.UU GlobalTheory.UU.RingPoint
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitCob
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}
namespace GlobalTheory.UU.UnitCob
theorem _root_.solution {U : Over S} {D : Type} [CommRing D] (e : Γ(U.left, ⊤) ≃+* D) (c : Multiplicative X →* Dˣ) :
    ∃ t : U ⟶ splitTorus S X, ∀ χ, e (chV t χ).val = (c (Multiplicative.ofAdd χ)).val :=
  ⟨(splitTorusPointsEquiv S X U).symm ((Units.map e.symm.toMonoidHom).comp c), fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; exact e.apply_symm_apply _⟩
end GlobalTheory.UU.UnitCob
