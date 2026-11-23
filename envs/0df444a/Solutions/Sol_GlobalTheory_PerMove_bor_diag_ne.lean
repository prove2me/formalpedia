-- Prove2me | solution 1 for GlobalTheory.PerMove.bor_diag_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:35.290983+00:00
-- url     : https://prove2.me/submissions/8ff894a0-57f9-45ec-9004-038059a22ef5

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
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ)
    (a : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ a a ≠ 0 := by
  have h := (hb τ).1
  rw [Matrix.det_of_upperTriangular (_root_.GlobalTheory.PerMove.bor_tri hb τ)] at h
  exact Finset.prod_ne_zero_iff.mp h a (Finset.mem_univ a)
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
