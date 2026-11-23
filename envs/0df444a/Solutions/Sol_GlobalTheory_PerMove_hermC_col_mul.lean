-- Prove2me | solution 1 for GlobalTheory.PerMove.hermC_col_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:50.938173+00:00
-- url     : https://prove2.me/submissions/26a1c699-3d9d-4558-b5f4-b0719fc3b050

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x b : Matrix (Fin r) (Fin r) ℂ)
    (a : Fin r) (w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (x * b) a) w = ∑ c, b c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (_root_.ReciprocityTheory.ChartRestriction.G.FD.col x c) w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
