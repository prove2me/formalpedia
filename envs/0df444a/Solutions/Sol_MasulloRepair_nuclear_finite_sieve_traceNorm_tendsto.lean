-- Prove2me | solution 1 for MasulloRepair.nuclear_finite_sieve_traceNorm_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T21:38:58.023142+00:00
-- url     : https://prove2.me/submissions/8f3d589f-a52c-4559-82cf-0e8ca4680055

import Theorems.Thm_MasulloRepair_nuclear_comp_left_sot_tendsto_traceNorm

open Filter Topology MasulloGRH
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem right_comp_finite_sieve_telescope
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (P : ℕ → H →L[ℂ] H) (n : ℕ) :
    (∑ i ∈ Finset.range n, (P i - P (i + 1)) ∘L A) =
      (P 0 - P n) ∘L A := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ext x
      simp [ContinuousLinearMap.comp_apply]

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A)
    (P : ℕ → H →L[ℂ] H) (Pinf : H →L[ℂ] H) (C : ℝ)
    (hbd : ∀ᶠ n in atTop, ‖P n‖ ≤ C)
    (hP : ∀ u : H, Tendsto (fun n => P n u) atTop (𝓝 (Pinf u))) :
    (∀ n, IsNuclearOperator ((P 0 - P n) ∘L A)) ∧
    IsNuclearOperator ((P 0 - Pinf) ∘L A) ∧
    Tendsto
      (fun n => traceNorm
        ((∑ i ∈ Finset.range n, (P i - P (i + 1)) ∘L A) -
          (P 0 - Pinf) ∘L A)) atTop (𝓝 0) ∧
    Tendsto
      (fun n => operatorTrace (∑ i ∈ Finset.range n, (P i - P (i + 1)) ∘L A)) atTop
        (𝓝 (operatorTrace ((P 0 - Pinf) ∘L A))) := by
  let Q : ℕ → H →L[ℂ] H := fun n => P 0 - P n
  let Q0 : H →L[ℂ] H := P 0 - Pinf
  have hbdQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ ‖P 0‖ + C := by
    filter_upwards [hbd] with n hn
    calc
      ‖Q n‖ = ‖P 0 - P n‖ := by rfl
      _ ≤ ‖P 0‖ + ‖P n‖ := norm_sub_le _ _
      _ ≤ ‖P 0‖ + C := by
        simpa [add_comm] using (add_le_add_right hn ‖P 0‖)
  have hQ : ∀ u : H, Tendsto (fun n => Q n u) atTop (𝓝 (Q0 u)) := by
    intro u
    have hconst : Tendsto (fun _ : ℕ => P 0 u) atTop (𝓝 (P 0 u)) :=
      tendsto_const_nhds
    have hsub := hconst.sub (hP u)
    simpa [Q, Q0] using hsub
  obtain ⟨hnuc, hnuc₀, hnorm, htrace⟩ :=
    MasulloRepair.nuclear_comp_left_sot_tendsto_traceNorm
      A hA atTop Q Q0 (‖P 0‖ + C) hbdQ hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    simpa [Q] using hnuc n
  · simpa [Q, Q0] using hnuc₀
  · have hfun :
        (fun n => traceNorm
          ((∑ i ∈ Finset.range n, (P i - P (i + 1)) ∘L A) -
            (P 0 - Pinf) ∘L A)) =
        (fun n => traceNorm
          (((P 0 - P n) ∘L A) - (P 0 - Pinf) ∘L A)) := by
      funext n
      rw [right_comp_finite_sieve_telescope]
    rw [hfun]
    simpa [Q, Q0] using hnorm
  · have hfun :
        (fun n => operatorTrace
          (∑ i ∈ Finset.range n, (P i - P (i + 1)) ∘L A)) =
        (fun n => operatorTrace ((P 0 - P n) ∘L A)) := by
      funext n
      rw [right_comp_finite_sieve_telescope]
    rw [hfun]
    simpa [Q, Q0] using htrace

