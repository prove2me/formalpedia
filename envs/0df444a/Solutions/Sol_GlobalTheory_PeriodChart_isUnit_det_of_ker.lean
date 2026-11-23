-- Prove2me | solution 1 for GlobalTheory.PeriodChart.isUnit_det_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:51.100873+00:00
-- url     : https://prove2.me/submissions/6c0dbd50-a87f-4f02-ba07-1db6c226919e

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
variable {g : ℕ}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (M : Matrix (Fin g) (Fin g) ℂ) (h : ∀ z, z ≠ 0 → M *ᵥ z ≠ 0) : IsUnit M.det := by
  rw [isUnit_iff_ne_zero]
  intro hd
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  exact h v hv h0
end GlobalTheory.PeriodChart
