-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_actualEdgeWeight_of_ratios
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/b081dda5-9d8c-4ca7-af4b-a5cf56624c21

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_plusProbability_of_ratios
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_minusProbability_raiseWeight_of_ratios

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt
          (plusProbability n (lam n) (mu n) i *
            minusProbability n (raiseWeight (lam n) i) (mu n) i))
      atTop (𝓝 (lagrangeWeight a b i * spectralAtom (a i))) := by
  have hplus := tendsto_plusProbability_of_ratios a b h
    lam mu hlam hmu i
  have hminus := tendsto_minusProbability_raiseWeight_of_ratios
    a b h lam mu hlam hmu i
  have hlimit := (hplus.mul hminus).sqrt
  have ha := h.ambient_nonneg i
  have hw := h.lagrangeWeight_pos i
  have hden : 0 < 2 * a i + 1 := by linarith
  convert hlimit using 1
  have hrad :
      (((a i + 1) / (2 * a i + 1)) * lagrangeWeight a b i) *
          ((a i / (2 * a i + 1)) * lagrangeWeight a b i) =
        (a i * (1 + a i)) *
          (lagrangeWeight a b i / (2 * a i + 1)) ^ 2 := by
    field_simp [hden.ne']
    ring
  rw [hrad, Real.sqrt_mul (mul_nonneg ha (by positivity)),
    Real.sqrt_sq (div_nonneg hw.le hden.le)]
  unfold spectralAtom quadraticCoordinate
  ring_nf
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
