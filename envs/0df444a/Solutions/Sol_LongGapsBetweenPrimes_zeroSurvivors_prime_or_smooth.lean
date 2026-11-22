-- Prove2me | solution 1 for LongGapsBetweenPrimes.zeroSurvivors_prime_or_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:33.268097+00:00
-- url     : https://prove2.me/submissions/7c0d654d-4fd6-4486-afdc-ccddb8c3d907

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_prime_or_smooth_of_survives

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} {H n : ℕ} (hx : 0 < x)
    (hsmall : 2 * (H : ℝ) < x * (coverW x : ℝ)) (hn : n ∈ zeroSurvivors x H) :
    n.Prime ∨ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ coverZ x := by
  obtain ⟨hnI, hsurvives⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnH⟩ := Finset.mem_Icc.mp hnI
  have h := prime_or_smooth_of_survives hn1 hnH hx hsmall (z := (coverZ x : ℝ))
  apply Or.imp_right (fun hs p hp hpn => by exact_mod_cast hs p hp hpn) (h ?_)
  intro p hp hrange hpn
  apply hsurvives p ?_ (Nat.mod_eq_zero_of_dvd hpn)
  simp only [zeroCoverPrimes, Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE]
  rcases hrange with hpW | ⟨hpZ, hpx⟩
  · exact Or.inl ⟨by exact_mod_cast hpW, hp⟩
  · refine Or.inr ⟨⟨Nat.le_floor hpx, hp⟩, ?_⟩
    rintro ⟨hpZ', _⟩
    exact (not_le_of_gt hpZ) (by exact_mod_cast hpZ')
end LongGapsBetweenPrimes
