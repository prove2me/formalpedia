-- Prove2me | solution 1 for GeneralCK.Reflection.ComplexDiscElementary.contactMap_contractionPackage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:03:46.9107+00:00
-- url     : https://prove2.me/submissions/12b14cfc-31dc-4c85-88f1-6cdb52ae1f1c

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_GeneralCK_complex_contact

/-!
# Exact elementary constants for the small-bias complex contraction

This file isolates the algebraic and metric-space part of the proposed
complex-disc construction.  The analytic estimates on the complex entropy
remain premises here: once they give the bounds `1103 / 1000` and `7 / 5`,
the results below prove that multiplication by a parameter of norm at most
`7 / 10` maps the closed `4 / 5` disc to itself and has Lipschitz constant
`49 / 50`.

No complex logarithm, fixed-point existence, or holomorphic dependence is
asserted by this module.
-/

namespace GeneralCK.Reflection.ComplexDiscElementary

open Set



/-- Exact multiplication of the parameter and entropy sup-norm bounds. -/
theorem contactMap_norm_le
    {E : ℂ → ℂ} {τ c : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    ‖contactMap E τ c‖ ≤ (7721 / 10000 : ℝ) := by
  rw [contactMap, Complex.norm_mul]
  calc
    ‖τ‖ * ‖E c‖ ≤ (7 / 10 : ℝ) * (1103 / 1000 : ℝ) :=
      mul_le_mul hτ hE (norm_nonneg _) (by norm_num)
    _ = (7721 / 10000 : ℝ) := by norm_num

/-- The image bound has strict room inside the chosen contact disc. -/
theorem contactMap_norm_lt_contactRadius
    {E : ℂ → ℂ} {τ c : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    ‖contactMap E τ c‖ < (4 / 5 : ℝ) :=
  (contactMap_norm_le hτ hE).trans_lt (by norm_num)

/-- A uniform entropy bound on the contact disc makes the scaled map a
self-map of that closed disc. -/
theorem contactMap_mapsTo_closedBall
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
      (Metric.closedBall 0 (4 / 5 : ℝ)) := by
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (contactMap_norm_lt_contactRadius hτ (hE c hc)).le



/-- Exact multiplication of the parameter and entropy difference bounds. -/
theorem contactMap_dist_le
    {E : ℂ → ℂ} {τ c d : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : dist (E c) (E d) ≤ (7 / 5 : ℝ) * dist c d) :
    dist (contactMap E τ c) (contactMap E τ d) ≤
      (49 / 50 : ℝ) * dist c d := by
  simp only [contactMap, dist_eq_norm] at hE ⊢
  rw [← mul_sub, Complex.norm_mul]
  calc
    ‖τ‖ * ‖E c - E d‖ ≤ (7 / 10 : ℝ) * ((7 / 5 : ℝ) * ‖c - d‖) :=
      mul_le_mul hτ hE (norm_nonneg _) (by norm_num)
    _ = (49 / 50 : ℝ) * ‖c - d‖ := by ring

/-- The entropy difference estimate composes to the advertised `49/50`
Lipschitz constant on the contact disc. -/
theorem contactMap_lipschitzOnWith
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : LipschitzOnWith (7 / 5 : NNReal) E
      (Metric.closedBall 0 (4 / 5 : ℝ))) :
    LipschitzOnWith (49 / 50 : NNReal) (contactMap E τ)
      (Metric.closedBall 0 (4 / 5 : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro c hc d hd
  simpa using contactMap_dist_le hτ (hE.dist_le_mul c hc d hd)









end GeneralCK.Reflection.ComplexDiscElementary

open Set
open GeneralCK.Reflection.ComplexDiscElementary
theorem solution
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hBound : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ))
    (hLip : LipschitzOnWith (7 / 5 : NNReal) E
      (Metric.closedBall 0 (4 / 5 : ℝ))) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
        (Metric.closedBall 0 (4 / 5 : ℝ)) ∧
      LipschitzOnWith (49 / 50 : NNReal) (contactMap E τ)
        (Metric.closedBall 0 (4 / 5 : ℝ)) :=
  ⟨contactMap_mapsTo_closedBall hτ hBound,
    contactMap_lipschitzOnWith hτ hLip⟩
