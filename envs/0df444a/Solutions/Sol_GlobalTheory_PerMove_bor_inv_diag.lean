-- Prove2me | solution 1 for GlobalTheory.PerMove.bor_inv_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:34.925958+00:00
-- url     : https://prove2.me/submissions/f24033c9-3e53-4f5f-89cd-a1538d458fd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Theorems.Thm_GlobalTheory_PerMove_bor_tri
import Theorems.Thm_GlobalTheory_PerMove_bor_inv_tri

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
    (a : Fin r) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)⁻¹ a a = (b τ a a)⁻¹ := by
  set M := _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ with hM
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr (hb τ).1)
  have h := congrFun (congrFun hmul a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a] at h
  · have hd : M a a = b τ a a := rfl
    rw [← hd]
    exact eq_inv_of_mul_eq_one_right h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hlt
    · rw [show M a k = 0 from _root_.GlobalTheory.PerMove.bor_tri hb τ hlt, zero_mul]
    · rw [show M⁻¹ k a = 0 from _root_.GlobalTheory.PerMove.bor_inv_tri hb τ hlt, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h
end _root_.GlobalTheory.PerMove
end GlobalTheory.PerMove
