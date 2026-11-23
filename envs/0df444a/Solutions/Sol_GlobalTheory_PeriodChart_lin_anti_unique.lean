-- Prove2me | solution 1 for GlobalTheory.PeriodChart.lin_anti_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.463419+00:00
-- url     : https://prove2.me/submissions/64b856ed-1f14-4f5b-ab56-d764b48e50f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (A A' C C' : V → V) (hA : ∀ z, A (Complex.I • z) = Complex.I • A z)
    (hA' : ∀ z, A' (Complex.I • z) = Complex.I • A' z) (hC : ∀ z, C (Complex.I • z) = -Complex.I • C z)
    (hC' : ∀ z, C' (Complex.I • z) = -Complex.I • C' z) (h : ∀ z, A z + C z = A' z + C' z) (z : V) :
    A z = A' z ∧ C z = C' z := by
  have h1 := h z
  have h2 := h (Complex.I • z)
  rw [hA, hA', hC, hC'] at h2
  have h3 : Complex.I • (A z - A' z) = Complex.I • (C z - C' z) := by
    linear_combination (norm := module) h2
  have h4 : A z - A' z = C z - C' z := smul_right_injective V Complex.I_ne_zero h3
  have h5 : (2 : ℂ) • (C z - C' z) = 0 := by
    linear_combination (norm := module) h1 - h4
  have hC0 : C z = C' z := by
    rcases smul_eq_zero.mp h5 with h6 | h6
    · norm_num at h6
    · exact sub_eq_zero.mp h6
  refine ⟨?_, hC0⟩
  rw [hC0] at h1
  exact add_right_cancel h1
end GlobalTheory.PeriodChart
