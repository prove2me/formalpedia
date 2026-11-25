-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.prod_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:06:47.393221+00:00
-- url     : https://prove2.me/submissions/120b1e0b-5ee3-4ad4-ba25-7558f4e3dd55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough

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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}
omit [GrpObj H]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {T : Over S} (t : T ⟶ H) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 4, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by
  rw [Fin.prod_univ_four]
  show h (lift t x ≫ ((fst H G ≫ i) * snd H G)).left ^ (1 : ℤ) * h (lift t x ≫ fst H G ≫ i).left ^ (-1 : ℤ) *
    h (lift t x ≫ snd H G).left ^ (-1 : ℤ) * h (lift t x ≫ (1 : H ⊗ G ⟶ G)).left ^ (1 : ℤ) = _
  rw [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]
end GlobalTheory.UU.PackageDescent
