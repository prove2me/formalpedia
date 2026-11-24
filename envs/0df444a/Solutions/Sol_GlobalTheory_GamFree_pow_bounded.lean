-- Prove2me | solution 1 for GlobalTheory.GamFree.pow_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:35.419826+00:00
-- url     : https://prove2.me/submissions/1c8796bb-abaf-4685-b7f7-bc4cf6ca8ed7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_bounded_pow_of_triangular_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GamFree
namespace GlobalTheory.GamFree
theorem _root_.solution {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (hb : b.BlockTriangular id) (hA : A.IsHermitian) (hm : ∀ i, FD.lminor A i ≠ 0)
    (hg : g * x = x * b) (hbA : bᵀ * A * b.map (starRingEnd ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by
  first
  | exact @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
  | exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
  | (apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)
  | (intros; apply _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry ..)
end GlobalTheory.GamFree
