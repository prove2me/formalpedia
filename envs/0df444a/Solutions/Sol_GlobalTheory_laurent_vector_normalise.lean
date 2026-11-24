-- Prove2me | solution 1 for GlobalTheory.laurent_vector_normalise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:57.08687+00:00
-- url     : https://prove2.me/submissions/414cb120-7d65-4691-aa3a-8e003f3f2b78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] (a : ℕ) (y : Fin a → HahnSeries ℤ k)
    (hy : y ≠ 0) : ∃ (f : HahnSeries ℤ k) (c0 : Fin a), f * y c0 = 1 ∧
      ∀ c, (f * y c).coeff (-1) = 0 := by
  classical
  have hne : (Finset.univ.filter fun c => y c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hy
    exact ⟨c, by simpa using hc⟩
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image _ (fun c => (y c).order) hne
  have h0 : y c0 ≠ 0 := by simpa using hc0
  refine ⟨(y c0)⁻¹, c0, inv_mul_cancel₀ h0, fun c => ?_⟩
  by_cases hc : y c = 0
  · simp [hc]
  · have h1 := hmin c (by simpa using hc)
    have h2 := HahnSeries.order_mul (inv_ne_zero h0) h0
    rw [inv_mul_cancel₀ h0, HahnSeries.order_one] at h2
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul (inv_ne_zero h0) hc]
    omega
end GlobalTheory
