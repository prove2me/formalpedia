-- Prove2me | solution 1 for MassEnergyEquivalence.invariantMass_zero_momentum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:32:21.066425+00:00
-- url     : https://prove2.me/submissions/27ae95a3-04b0-4611-b4ea-667f12c13887

import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_MassEnergyEquivalence_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MassEnergyEquivalence Filter Asymptotics Topology

/-- When the total three-momentum vanishes, the invariant mass is the
nonnegative total energy divided by the speed of light squared. -/
theorem solution {ι : Type*} (s : Finset ι) (c : ℝ) (m : ι → ℝ)
    (v : ι → Vec3) (hc : 0 < c) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hv : ∀ i ∈ s, ‖v i‖ < c)
    (hp : ∑ i ∈ s, relMomentum c (m i) (v i) = 0) :
    invariantMass s c m v =
      (∑ i ∈ s, relEnergy c (m i) (v i)) / c ^ 2 := by
  have hgamma (i : ι) : 0 ≤ lorentzFactor c (v i) := by
    unfold lorentzFactor
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hE (i : ι) (hi : i ∈ s) : 0 ≤ relEnergy c (m i) (v i) := by
    unfold relEnergy
    exact mul_nonneg (mul_nonneg (hgamma i) (hm i hi)) (sq_nonneg c)
  have hsum : 0 ≤ ∑ i ∈ s, relEnergy c (m i) (v i) := by
    exact Finset.sum_nonneg (fun i hi => hE i hi)
  unfold invariantMass
  rw [hp]
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum]
