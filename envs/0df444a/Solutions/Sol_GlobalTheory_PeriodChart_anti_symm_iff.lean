-- Prove2me | solution 1 for GlobalTheory.PeriodChart.anti_symm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:23.571801+00:00
-- url     : https://prove2.me/submissions/c005a9bd-a650-460a-835c-f3534cf0f5d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
import Theorems.Thm_GlobalTheory_PeriodChart_anti_apply
import Theorems.Thm_GlobalTheory_PeriodChart_star_single
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_mulVec_left

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
theorem _root_.solution (G Z : Matrix (Fin g) (Fin g) ℂ) :
    (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ↔ (Gᵀ * Z)ᵀ = Gᵀ * Z := by
  have key : ∀ z w, sesq G (anti Z z) w = star z ⬝ᵥ ((Zᵀ * G) *ᵥ star w) := by
    intro z w
    rw [anti_apply, sesq_mulVec_left, sesq_apply, hermForm]
  have tr : (Gᵀ * Z)ᵀ = Zᵀ * G := by rw [transpose_mul, transpose_transpose]
  constructor
  · intro h
    rw [tr]
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [key, key, star_single, star_single] at this
    have e1 : (Pi.single i (1 : ℂ) : Fin g → ℂ) ⬝ᵥ ((Zᵀ * G) *ᵥ Pi.single j 1) = (Zᵀ * G) i j := by
      simp [mulVec, dotProduct, Pi.single_apply]
    have e2 : (Pi.single j (1 : ℂ) : Fin g → ℂ) ⬝ᵥ ((Zᵀ * G) *ᵥ Pi.single i 1) = (Zᵀ * G) j i := by
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [e1, e2] at this
    rw [this, ← transpose_apply (Zᵀ * G) i j, transpose_mul, transpose_transpose]
  · intro h z w
    have e : Zᵀ * G = Gᵀ * Z := tr.symm.trans h
    have hM : (Zᵀ * G)ᵀ = Zᵀ * G := by rw [transpose_mul, transpose_transpose, e]
    rw [key, key, dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
end GlobalTheory.PeriodChart
