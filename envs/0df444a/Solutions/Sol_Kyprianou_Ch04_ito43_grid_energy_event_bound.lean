-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_grid_energy_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:05:20.114888+00:00
-- url     : https://prove2.me/submissions/2949f48c-43c5-472a-8553-91171131effc

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_energy_localised_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_grid_cosine_mean_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_kernel_measurable_bound
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
import Theorems.Thm_Kyprianou_Ch04_ito43_real_measurable_tail
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (M : Ω → ℝ) (T R : NNReal) (hR : 0 < R)
    (r D : ℝ) (hr : (R : ℝ) = 2*r)
    (hm : ∀ᵐ w ∂P, ∀ a ≤ T, |X a w| ≤ M w)
    (n : ℕ) (hn : 0 < n) :
    let A : ℝ := Real.pi^2*(R : ℝ)^2/2
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let F : Ω → ℝ := fun w => ∑ k ∈ Finset.range n,
      (1 - Real.cos ((1/(R : ℝ)) * (X (u (k+1)) w - X (u k) w)))
    (P {w | ∃ t : NNReal, t ≤ T ∧
      let v : ℕ → NNReal := fun k => min t (u k)
      A*D+(R : ℝ)^2+1 ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2}).toReal ≤
      (P {w | r < M w}).toReal + (P {w | D ≤ F w}).toReal := by
  intro A u F
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let U : Set Ω := {w | r < M w}
  let V : Set Ω := {w | D ≤ F w}
  let W : Set Ω := {w | ∃ t : NNReal, t ≤ T ∧
    let v : ℕ → NNReal := fun k => min t (u k)
    A*D+(R : ℝ)^2+1 ≤ ∑ k ∈ Finset.range n, (X (v (k+1)) w-X (v k) w)^2}
  have hsub : ∀ᵐ w ∂P, w ∈ W → w ∈ U ∪ V := by
    filter_upwards [hm] with w hw
    rintro ⟨t,ht,htE⟩
    by_cases hbad : r < M w
    · exact Or.inl hbad
    right
    by_contra hsmall
    have hb (a b : NNReal) (ha : a ≤ T) (hb : b ≤ T) : |X a w-X b w| ≤ (R : ℝ) := by
      have h1 := hw a ha
      have h2 := hw b hb
      rw [hr]
      exact (abs_sub _ _).trans (by linarith [le_of_not_gt hbad])
    have H := Kyprianou.Ch04.ito43_grid_energy_localised_bound (fun s => X s w) T R t hR ht n hn hb
    change A*D+(R : ℝ)^2+1 ≤ _ at htE
    have hcos : (∑ k ∈ Finset.range n, (1 - Real.cos ((X (u (k+1)) w-X (u k) w)/(R : ℝ)))) = F w := by
      apply Finset.sum_congr rfl
      intro k hk
      ring_nf
    dsimp only at H
    rw [hcos] at H
    change _ ≤ A*F w+(R : ℝ)^2 at H
    change ¬ D ≤ F w at hsmall
    linarith [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hsmall)) hA]
  have hW : (P W).toReal ≤ (P U).toReal+(P V).toReal := by
    change P.real W ≤ P.real U+P.real V
    exact (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans (measureReal_union_le _ _)
  exact hW
