-- Prove2me | solution 1 for GlobalTheory.FormalCalc.ext_of_pderiv_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:09.088669+00:00
-- url     : https://prove2.me/submissions/1abf93aa-2902-4096-aecb-98fef62ed27d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Theorems.Thm_GlobalTheory_FormalCalc_natCast_mul_coeff_of_pderiv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ ι A : Type*} [CommRing A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution [IsAddTorsionFree A] (e : ι → σ) {f g : MvPowerSeries σ A}
    (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = coeff α g) : f = g := by
  ext α
  by_cases h : ∀ i, α (e i) = 0
  · exact h0 α h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 := natCast_mul_coeff_of_pderiv_eq (hD i) hi
  have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e i) g = _) hi
  rw [← h2, ← nsmul_eq_mul, ← nsmul_eq_mul] at h1
  exact (smul_right_inj hi).mp h1
end GlobalTheory.FormalCalc
