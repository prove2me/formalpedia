-- Prove2me | solution 1 for GlobalTheory.LocLift.dim_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:37.111891+00:00
-- url     : https://prove2.me/submissions/406632fd-8b81-4dfd-b566-e5b7fa051b83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_PeriodDatum_two_mul_eq_of_isTypeFn


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
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {p q : ℕ} {ty : Fin g → (E →+* ℂ)}
    (hty : IsTypeFn H p q ty) : Module.finrank ℚ E / 2 * (p + q) = g := by
  have h := PeriodDatum.two_mul_eq_of_isTypeFn H hty
  rw [IsTotallyComplex.finrank E] at h ⊢
  rw [Nat.mul_div_cancel_left _ two_pos]
  rw [_root_.mul_assoc] at h
  omega
end GlobalTheory.LocLift
