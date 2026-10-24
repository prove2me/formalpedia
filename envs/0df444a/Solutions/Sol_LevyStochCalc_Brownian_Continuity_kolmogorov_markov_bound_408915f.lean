-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.kolmogorov_markov_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:37:31.054475+00:00
-- url     : https://prove2.me/submissions/762ef034-2694-404a-aafd-4f16d5d6860a

import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLS408915f_LevyStochCalc_Brownian_ContinuityDyadicChaining
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityKolmogorovBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Brownian
end LevyStochCalc.Brownian
open LevyStochCalc LevyStochCalc.Brownian
section
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Continuity
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
namespace LevyStochCalc.Brownian.Continuity
end LevyStochCalc.Brownian.Continuity
open LevyStochCalc.Brownian.Continuity in
/-- **Markov / Chebyshev bound from the Kolmogorov condition.**

For a process satisfying the Kolmogorov moment condition
`∫⁻ ω, edist (X s ω) (X t ω)^p ∂P ≤ M · edist s t ^ q` and any threshold
`0 < lam < ⊤`,

  `P {ω | lam ≤ edist (X s ω) (X t ω)} ≤ M · edist s t ^ q / lam ^ p`.

This is the per-pair tail bound underlying both the convergence-in-measure
argument (`kolmogorov_modification_ae_eq`) and the per-dyadic-level Borel–
Cantelli step of the continuous-modification construction. -/
lemma solution
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
    P {ω | lam ≤ edist (X s ω) (X t ω)}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p := by
  have hp_pos : 0 < p := hX.p_pos
  -- {lam ≤ edist} = {lam^p ≤ edist^p} since `· ^ p` is strictly monotone.
  have h_set_eq :
      {ω | lam ≤ edist (X s ω) (X t ω)}
        = {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p} := by
    ext ω; exact (ENNReal.rpow_le_rpow_iff hp_pos).symm
  have h_edist_aemeas : AEMeasurable
      (fun ω => edist (X s ω) (X t ω) ^ p) P :=
    ((hX.measurable_edist (s := s) (t := t)).pow_const p).aemeasurable
  have h_Kol : ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
      ≤ (M : ℝ≥0∞) * edist s t ^ q := hX.kolmogorovCondition s t
  have h_Markov :
      lam ^ p * P {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p}
        ≤ ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P :=
    MeasureTheory.mul_meas_ge_le_lintegral₀ h_edist_aemeas (lam ^ p)
  have h_chain :
      lam ^ p * P {ω | lam ≤ edist (X s ω) (X t ω)}
        ≤ (M : ℝ≥0∞) * edist s t ^ q := by
    rw [h_set_eq]; exact le_trans h_Markov h_Kol
  have hlamp_pos : 0 < lam ^ p := by
    apply ENNReal.rpow_pos_of_nonneg hlam_pos
    exact hp_pos.le
  have hlamp_ne_top : lam ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp_pos.le hlam_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hlamp_pos.ne') (Or.inl hlamp_ne_top),
      mul_comm]
  exact h_chain
