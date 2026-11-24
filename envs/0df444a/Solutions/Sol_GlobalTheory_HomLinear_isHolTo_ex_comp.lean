-- Prove2me | solution 1 for GlobalTheory.HomLinear.isHolTo_ex_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:39.2421+00:00
-- url     : https://prove2.me/submissions/0185f1cf-f10a-48c6-91cc-a23e4d455afb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom
import Theorems.Thm_P2M_GlobalTheory_HomLinear_valAt__comp_left_59bd74891c19
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
omit [GrpObj A']
namespace GlobalTheory.HomLinear
theorem _root_.solution (u : HolUnif A L g) (f : A ⟶ A') :
    IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (u.ex z ≫ f).left) := by
  intro U s
  have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
    ext w
    simp
  have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
      fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
    funext fun w => valAt'_comp_left _ f U s
  rw [hset, hfun]
  exact u.hol _ _
end GlobalTheory.HomLinear
