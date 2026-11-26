-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_finite_jump_energy_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:21:50.880779+00:00
-- url     : https://prove2.me/submissions/936c4ebc-884c-410f-ab4b-f84f0d61b998

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_finite_jump_energy_lower
open Filter Set
open scoped NNReal Topology
set_option autoImplicit false

/-- A cadlag path whose full-grid squared increments are frequently bounded has square-summable jumps. -/
theorem solution (Y L : NNReal → ℝ) (T : NNReal) (hT : 0 < T)
    (hR : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hL : ∀ t, 0 < t → Tendsto Y (nhdsWithin t (Iio t)) (nhds (L t)))
    (C : ℝ)
    (hQ : ∃ᶠ n : ℕ in atTop, (∑ k ∈ Finset.range (n+1),
      (Y (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) -
       Y (T*(k : NNReal)/((n+1 : ℕ) : NNReal)))^2) < C) :
    Summable (fun t : Ioc (0 : NNReal) T => (Y t-L t)^2) ∧
      (∑' t : Ioc (0 : NNReal) T, (Y t-L t)^2) ≤ C := by
  classical
  let f : Ioc (0 : NNReal) T → ℝ := fun t => (Y t-L t)^2
  have hsum (S : Finset (Ioc (0 : NNReal) T)) : ∑ t ∈ S, f t ≤ C := by
    by_contra! h
    let A := S.image Subtype.val
    have ha : ∀ t ∈ A, 0 < t ∧ t ≤ T := by
      intro t ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
      exact x.property
    have hA : (∑ t ∈ A, (Y t-L t)^2) = ∑ t ∈ S, f t :=
      Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)
    have hlower := Kyprianou.Ch04.ito43_finite_jump_energy_lower Y L T hT hR hL A ha C
      (hA ▸ h)
    obtain ⟨n,hn⟩ := (hQ.and_eventually hlower).exists
    exact (not_lt_of_ge hn.2) hn.1
  have hs : Summable f := summable_of_sum_le (fun _ => sq_nonneg _) hsum
  exact ⟨hs,hs.tsum_le_of_sum_le hsum⟩
