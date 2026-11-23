-- Prove2me | solution 1 for GlobalTheory.SocleDet.coeff_eq_zero_of_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:00.076659+00:00
-- url     : https://prove2.me/submissions/04d62c13-15e6-48de-a748-403cd16ed9d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SocleDet
open Matrix
open MvPowerSeries
variable {k : Type*} [CommRing k] {σ : Type*}
namespace GlobalTheory.SocleDet
theorem _root_.solution (N : ℕ) (S : Set σ) (p : MvPowerSeries σ k)
    (hp : p ∈ Ideal.span ((fun i => (X i : MvPowerSeries σ k) ^ N) '' S))
    (m : σ →₀ ℕ) (hm : ∀ j ∈ S, m j < N) : coeff m p = 0 := by
  classical
  obtain ⟨t, ht, c, rfl⟩ := (Submodule.mem_span_image_iff_exists_fun _).1 hp
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact X_pow_dvd_iff.1 (Dvd.intro_left _ rfl) m (hm j (ht j.2))
end GlobalTheory.SocleDet
