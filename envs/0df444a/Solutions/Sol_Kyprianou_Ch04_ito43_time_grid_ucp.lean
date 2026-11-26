-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_time_grid_ucp
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:25:06.723782+00:00
-- url     : https://prove2.me/submissions/0d49af28-b88f-4359-a011-432afb1a026b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_continuous_kernel_ucp
import Theorems.Thm_Kyprianou_Ch04_ito43_time_slice_derivative
import Theorems.Thm_Kyprianou_Ch04_ito43_time_slice_ftc
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Reduce time increment convergence to the continuous-kernel stopped grid integral. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hLevy : IsLevyProcess X P)
    (f : ℝ × ℝ → ℝ)
    (hfJointC1 : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) :
    ∀ (T : NNReal) (epsilon : ℝ), 0 < epsilon →
      Tendsto (fun n : ℕ => (P {w | ∃ t : NNReal, t ≤ T ∧
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        epsilon ≤ |(∫ s in Icc (0 : ℝ) (t : ℝ),
          fderiv ℝ f (s,X (Real.toNNReal s) w) (1,0)) -
          (∑ k ∈ Finset.range n,
            (f ((v (k+1) : ℝ), X (v (k+1)) w) -
              f ((v k : ℝ), X (v (k+1)) w)))|}).toReal) atTop (nhds 0) := by
  intro T e he
  let S := Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
  let g := fun z : ℝ × ℝ => fderivWithin ℝ f S z (1,0)
  obtain ⟨hg,heq⟩ := Kyprianou.Ch04.ito43_time_slice_derivative f hfJointC1
  have H := Kyprianou.Ch04.ito43_continuous_kernel_ucp P X hLevy g hg T e he
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hpoint (t : NNReal) (w : Omega) :
      (∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) =
      ∫ s in Icc (0 : ℝ) (t : ℝ),
        fderiv ℝ f (s,X (Real.toNNReal s) w) (1,0) := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact heq s hs.1 _
  let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
  have hu : Monotone u := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) (by positivity)) (by positivity)
  have hcell (t : NNReal) (w : Omega) (k : ℕ) :
      (∫ s in Icc (min t (u k) : ℝ) (min t (u (k+1)) : ℝ),
        g (s,X (min t (u (k+1))) w)) =
      f ((min t (u (k+1)) : ℝ),X (min t (u (k+1))) w) -
        f ((min t (u k) : ℝ),X (min t (u (k+1))) w) := by
    exact Kyprianou.Ch04.ito43_time_slice_ftc f hfJointC1 _ _ _
      (by positivity) (by exact_mod_cast min_le_min_left t (hu (Nat.le_succ k)))
  congr 1
  apply congrArg P
  ext w
  change (∃ t : NNReal, t ≤ T ∧ _) ↔ (∃ t : NNReal, t ≤ T ∧ _)
  apply exists_congr
  intro t
  let v : ℕ → NNReal := fun k => min t (u k)
  have hsum :
      (∑ k ∈ Finset.range n, (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ),
        g (s,X (v (k+1)) w))) =
      ∑ k ∈ Finset.range n, (f ((v (k+1) : ℝ),X (v (k+1)) w) -
        f ((v k : ℝ),X (v (k+1)) w)) :=
    Finset.sum_congr rfl fun k _ => hcell t w k
  change (t ≤ T ∧ e ≤ |(∫ s in Icc (0 : ℝ) (t : ℝ), g (s,X (Real.toNNReal s) w)) -
    (∑ k ∈ Finset.range n, (∫ s in Icc (v k : ℝ) (v (k+1) : ℝ),
      g (s,X (v (k+1)) w)))|) ↔
    (t ≤ T ∧ e ≤ |(∫ s in Icc (0 : ℝ) (t : ℝ),
      fderiv ℝ f (s,X (Real.toNNReal s) w) (1,0)) -
      (∑ k ∈ Finset.range n, (f ((v (k+1) : ℝ),X (v (k+1)) w) -
        f ((v k : ℝ),X (v (k+1)) w)))|)
  rw [hpoint, hsum]
