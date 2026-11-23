-- Prove2me | solution 1 for GlobalTheory.PerMove.bor_inv_tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.091749+00:00
-- url     : https://prove2.me/submissions/9a3a497e-4ff7-43a5-a295-d8e82ca3fca9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Theorems.Thm_GlobalTheory_PerMove_bor_tri

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
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹.BlockTriangular id := by
  letI := (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (hb τ).1)
  exact Matrix.blockTriangular_inv_of_blockTriangular (_root_.GlobalTheory.PerMove.bor_tri hb τ)
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
