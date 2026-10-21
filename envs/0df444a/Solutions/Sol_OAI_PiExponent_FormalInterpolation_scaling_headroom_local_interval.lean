-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaling_headroom_local_interval
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:59:15.758171+00:00
-- url     : https://prove2.me/submissions/24e3b3d0-d9ff-440c-9a42-99fc290fda8e

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

open scoped BigOperators Topology
open OAI.PiExponent.FormalInterpolation

theorem solution
    (m : Nat) (A B : Real) (c d : Fin m -> Real)
    (hA : A < 1) (hB : B < 1)
    (hcd : forall i, c i < d i) :
    exists ε : Real, 0 < ε ∧
      forall x : Real, 1 < x → x < 1 + ε →
        (x ^ (m + 1) * A < 1) ∧
        (x ^ m * B < 1) ∧
        (forall i, x * c i < d i) := by
  have hAev : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ^ (m + 1) * A < 1 := by
    have hAt : (1 : ℝ) ^ (m + 1) * A < 1 := by simpa using hA
    have hcont : ContinuousAt (fun x : ℝ => x ^ (m + 1) * A) 1 := by fun_prop
    exact hcont.eventually (isOpen_Iio.mem_nhds hAt)
  have hBev : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ^ m * B < 1 := by
    have hBt : (1 : ℝ) ^ m * B < 1 := by simpa using hB
    have hcont : ContinuousAt (fun x : ℝ => x ^ m * B) 1 := by fun_prop
    exact hcont.eventually (isOpen_Iio.mem_nhds hBt)
  have hlin : ∀ i : Fin m, ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x * c i < d i := by
    intro i
    have hit : (1 : ℝ) * c i < d i := by simpa using hcd i
    have hcont : ContinuousAt (fun x : ℝ => x * c i) 1 := by fun_prop
    exact hcont.eventually (isOpen_Iio.mem_nhds hit)
  have hlinev : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), ∀ i : Fin m, x * c i < d i := by
    exact Filter.eventually_all.mpr hlin
  have hall : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ),
      (x ^ (m + 1) * A < 1) ∧ (x ^ m * B < 1) ∧ (∀ i : Fin m, x * c i < d i) := by
    filter_upwards [hAev, hBev, hlinev] with x hAx hBx hcx
    exact ⟨hAx, hBx, hcx⟩
  change {x : ℝ | (x ^ (m + 1) * A < 1) ∧ (x ^ m * B < 1) ∧
      (∀ i : Fin m, x * c i < d i)} ∈ 𝓝 (1 : ℝ) at hall
  rcases Metric.mem_nhds_iff.mp hall with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro x hx1 hxε
  have hdist : dist x (1 : ℝ) < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < x - 1)]
    linarith
  have hxball : x ∈ Metric.ball (1 : ℝ) ε := by
    simpa [Metric.mem_ball] using hdist
  exact hball hxball