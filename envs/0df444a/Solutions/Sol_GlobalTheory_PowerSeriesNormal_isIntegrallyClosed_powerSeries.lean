-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNormal.isIntegrallyClosed_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:36.249662+00:00
-- url     : https://prove2.me/submissions/0f484a31-8a9b-4a24-90fd-570361f21f0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_dvd_of_pow_dvd_powerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.PowerSeriesNormal
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R], IsIntegrallyClosed (PowerSeries R) := by
  intro R _ _ _ _
  let K := FractionRing R⟦X⟧
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨⟨f, ⟨g, hg⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R⟦X⟧) x
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  set x := IsLocalization.mk' K f (⟨g, hg⟩ : nonZeroDivisors R⟦X⟧) with hxdef
  have hgx : algebraMap R⟦X⟧ K g * x = algebraMap R⟦X⟧ K f := by
    rw [mul_comm, hxdef]; exact IsLocalization.mk'_spec K f ⟨g, hg⟩
  obtain ⟨p, hp, hpx⟩ := hx
  have hpx' : Polynomial.aeval x p = 0 := by rw [Polynomial.aeval_def]; exact hpx
  have key : ∀ n : ℕ, g ^ n ∣ g ^ p.natDegree * f ^ n := by
    intro n
    set q := (Polynomial.X ^ n : Polynomial R⟦X⟧) %ₘ p
    have hq : Polynomial.aeval x q = x ^ n := by
      rw [Polynomial.aeval_modByMonic_eq_self_of_root hpx']; simp
    have hqd : q.natDegree ≤ p.natDegree := Polynomial.natDegree_modByMonic_le _ hp
    have hterm : ∀ i ≤ p.natDegree, algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ i =
        algebraMap R⟦X⟧ K (g ^ (p.natDegree - i) * f ^ i) := by
      intro i hi
      calc algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ i
          = algebraMap R⟦X⟧ K g ^ (p.natDegree - i) * (algebraMap R⟦X⟧ K g * x) ^ i := by
            rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hi]
        _ = algebraMap R⟦X⟧ K (g ^ (p.natDegree - i) * f ^ i) := by
            rw [hgx, map_mul, map_pow, map_pow]
    have hz : algebraMap R⟦X⟧ K g ^ p.natDegree * x ^ n = algebraMap R⟦X⟧ K
        (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (g ^ (p.natDegree - i) * f ^ i)) := by
      rw [← hq, Polynomial.aeval_eq_sum_range, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ p.natDegree := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hqd
      rw [Algebra.smul_def, mul_left_comm, hterm i hi']
      simp only [map_mul]
    refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (g ^ (p.natDegree - i) * f ^ i),
      IsFractionRing.injective R⟦X⟧ K ?_⟩
    rw [map_mul, map_mul, ← hz, map_pow, map_pow, ← hgx, map_pow]
    ring
  obtain ⟨y, hy⟩ := dvd_of_pow_dvd_powerSeries hg0 (pow_ne_zero _ hg0) key
  refine ⟨y, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hy, map_mul, mul_comm]
end GlobalTheory.PowerSeriesNormal
