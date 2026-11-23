-- Prove2me | solution 1 for GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:16.128324+00:00
-- url     : https://prove2.me/submissions/91eca042-5e79-4697-889f-887e1b78dee6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {x y : ℂ} (h : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃) :
    ∃ z ∉ L.lattice, ℘[L] z = x ∧ ℘'[L] z = y := by
  obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
  rw [← L.derivWeierstrassP_sq z hz] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨z, hz, rfl, h.symm⟩
  · exact ⟨-z, by simpa using hz, by simp, by simp [h]⟩
end GlobalTheory
