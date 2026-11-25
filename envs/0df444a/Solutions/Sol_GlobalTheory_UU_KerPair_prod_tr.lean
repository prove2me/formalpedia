-- Prove2me | solution 1 for GlobalTheory.UU.KerPair.prod_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:40.976115+00:00
-- url     : https://prove2.me/submissions/723e6b91-aa85-436f-ae94-74b3c0a71df5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOfGen

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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.KerPair
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}
omit [IsCommMonObj B]
namespace GlobalTheory.UU.KerPair
theorem _root_.solution {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) (m : ℤ) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ ((![1, -1] : Fin 2 → ℤ) k * m) =
      h ((ρ ≫ x) * b).left ^ m * h b.left ^ (-m) := by
  have e₀ : (lift ρ b).left ≫ trφ x 0 = ((ρ ≫ x) * b).left := by
    show (lift ρ b ≫ ((fst T B ≫ x) * snd T B)).left = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
  have e₁ : (lift ρ b).left ≫ trφ x 1 = b.left := by
    show (lift ρ b ≫ snd T B).left = _
    rw [lift_snd]
  rw [Fin.prod_univ_two, e₀, e₁]
  simp
end GlobalTheory.UU.KerPair
