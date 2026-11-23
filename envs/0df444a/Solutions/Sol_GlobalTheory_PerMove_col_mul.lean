-- Prove2me | solution 1 for GlobalTheory.PerMove.col_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:34.875712+00:00
-- url     : https://prove2.me/submissions/b20e0a82-b991-46fa-86f9-f8a7305830f5

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
namespace GlobalTheory.PerMove
namespace _root_.GlobalTheory.PerMove
theorem _root_.solution (g x : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (g * x) a = g *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col x a := by
  ext i
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
