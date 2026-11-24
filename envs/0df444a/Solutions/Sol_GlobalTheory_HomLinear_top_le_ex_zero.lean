-- Prove2me | solution 1 for GlobalTheory.HomLinear.top_le_ex_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:56.443818+00:00
-- url     : https://prove2.me/submissions/2f9a509a-3bcc-4096-9605-e161ff7d506c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVarietStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsLinearOfIsMonHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HomLinear
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
namespace GlobalTheory.HomLinear
theorem _root_.solution (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).mpr u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h0, ← hv]
  intro a _
  exact h (Set.mem_univ _)
end GlobalTheory.HomLinear
