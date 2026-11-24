-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_density_pointwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T09:43:50.1879+00:00
-- url     : https://prove2.me/submissions/ef21c150-4086-4332-ad0d-5c5e12b7bc55

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08 Kyprianou.Ch08.StageB Topology

theorem solution
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q x : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hW : IsQScale ψ q (W q))
    (hm : Monotone (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r))
    (hl : Tendsto (fun r : ℝ => Real.exp (-(Phi ψ q) * r) * W q r) atTop (𝓝 (deriv (Phi ψ) q))):
    let f : ℕ → ℝ → ℝ≥0∞ := fun n y => if 0 ≤ y + (n : ℝ) - x then
      ENNReal.ofReal (Real.exp (-(Phi ψ q) * (y - x)) *
        (Real.exp (-(Phi ψ q) * (n : ℝ)) * W q n) - W q (x - y))
      else 0
    ∀ y : ℝ, Tendsto (fun n : ℕ => f n y) atTop
      (𝓝 (ENNReal.ofReal (unrestrictedPotentialDensity ψ q (W q) (y-x)))) := by
  classical
  intro f y
  have hV := hl.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := ENNReal.tendsto_ofReal
    ((tendsto_const_nhds (x := Real.exp (-(Phi ψ q) * (y-x)))).mul hV |>.sub
      (tendsto_const_nhds (x := W q (x-y))))
  have he : ∀ᶠ n : ℕ in atTop, 0 ≤ y + (n : ℝ) - x := by
    obtain ⟨N, hN⟩ := exists_nat_ge (x-y)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hc : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have heq : -(y-x) = x-y := by ring
  unfold unrestrictedPotentialDensity
  rw [heq, mul_comm (deriv (Phi ψ) q)]
  apply h.congr'
  filter_upwards [he] with n hn
  simp only [f, if_pos hn, Function.comp_apply]
