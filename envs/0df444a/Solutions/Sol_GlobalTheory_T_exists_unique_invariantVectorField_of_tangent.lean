-- Prove2me | solution 1 for GlobalTheory.T.exists_unique_invariantVectorField_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:38.603949+00:00
-- url     : https://prove2.me/submissions/b0ba81e4-ee51-4b09-9734-6be1c84fedbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Theorems.Thm_GlobalTheory_KS_InvField_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  first | exact @GlobalTheory.KS.InvField.main | exact GlobalTheory.KS.InvField.main | (intros; apply GlobalTheory.KS.InvField.main <;> assumption)
end _root_.GlobalTheory.T
