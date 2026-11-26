-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_full_grid_energy_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:05.286065+00:00
-- url     : https://prove2.me/submissions/19e3c7b8-025d-459f-8ebf-b7a7d00c48af

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A bound for the stopped energy at all times bounds the full grid along the positive mesh sequence. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (T : NNReal) (C η : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,
      (P {w | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        C ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2}).toReal ≤ η) :
    ∀ᶠ n : ℕ in atTop, (P {w | C ≤ ∑ k ∈ Finset.range (n+1),
      (X (T*((k+1 : ℕ) : NNReal)/((n+1 : ℕ) : NNReal)) w -
       X (T*(k : NNReal)/((n+1 : ℕ) : NNReal)) w)^2}).toReal ≤ η := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  apply eventually_atTop.mpr
  refine ⟨N,fun n hn => ?_⟩
  have H := hN (n+1) (hn.trans (Nat.le_succ n))
  refine (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono ?_)).trans H
  intro w hw
  refine ⟨T,le_rfl,?_⟩
  let u : ℕ → NNReal := fun k => T*(k : NNReal)/((n+1 : ℕ) : NNReal)
  have hu (k : ℕ) (hk : k ≤ n+1) : u k ≤ T := by
    dsimp [u]
    apply (div_le_iff₀ (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (by positivity)
  change C ≤ ∑ k ∈ Finset.range (n+1),
    (X (min T (u (k+1))) w-X (min T (u k)) w)^2
  change C ≤ ∑ k ∈ Finset.range (n+1), (X (u (k+1)) w-X (u k) w)^2 at hw
  apply hw.trans_eq
  apply Finset.sum_congr rfl
  intro k hk
  rw [min_eq_right (hu (k+1) (Finset.mem_range.mp hk)),
    min_eq_right (hu k (Nat.le_of_lt (Finset.mem_range.mp hk)))]
