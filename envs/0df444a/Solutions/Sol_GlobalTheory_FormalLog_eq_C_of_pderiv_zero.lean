-- Prove2me | solution 1 for GlobalTheory.FormalLog.eq_C_of_pderiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:11.012441+00:00
-- url     : https://prove2.me/submissions/6bad4bc3-6590-458f-9d4a-80f8b737b44d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqCOfPderivZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {σ τ : Type}
namespace GlobalTheory.FormalLog
theorem _root_.solution [Algebra ℚ k] {g : MvPowerSeries τ k} (h : ∀ v, pderiv k v g = 0) :
    g = C (constantCoeff g) := by
  classical
  ext n
  rw [coeff_C]
  split_ifs with hn
  · subst hn; rfl
  · obtain ⟨v, hv⟩ : ∃ v, n v ≠ 0 := by
      by_contra hc; push Not at hc; exact hn (Finsupp.ext hc)
    have hle : Finsupp.single v 1 ≤ n := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hv)
    have h1 := congrArg (coeff (n - Finsupp.single v 1)) (h v)
    rw [coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have hc' : (n - Finsupp.single v 1 : τ →₀ ℕ) v + 1 = n v := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    have hc : (((n - Finsupp.single v 1 : τ →₀ ℕ) v : ℕ) : k) + 1 = ((n v : ℕ) : k) := by
      rw [← hc']; push_cast; ring
    rw [hc] at h1
    have hu : IsUnit ((n v : ℕ) : k) := by
      have : ((n v : ℕ) : k) = algebraMap ℚ k (n v : ℚ) := by simp
      rw [this]; exact (IsUnit.mk0 _ (by exact_mod_cast hv)).map _
    rcases hu with ⟨w, hw⟩
    rw [← hw] at h1
    simpa using congrArg (· * ((w⁻¹ : kˣ) : k)) h1
end GlobalTheory.FormalLog
