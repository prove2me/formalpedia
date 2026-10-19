-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_Gamma_of_stieltjesPhaseProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/9ad5227f-940c-428d-bb49-71868e8c69da

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r j : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
    (h : ∀ n, Interlacing (a n) (b n))
    (hAB : Interlacing A B) (c : ℝ)
    (hproduct : ∀ t : ℝ, 0 < t →
      Tendsto (fun n => stieltjesPhaseProduct (a n) (b n) t)
        atTop (𝓝 (c * stieltjesPhaseProduct A B t))) :
    Tendsto (fun n => Gamma (a n) (b n))
      atTop (𝓝 ((1 - c) / 2 + c * Gamma A B)) := by
  have hlimit :=
    tendsto_one_sub_two_mul_Gamma_of_stieltjesPhaseProduct
      a b A B h hAB c hproduct
  have hrecover := ((tendsto_const_nhds
    (x := (1 : ℝ))).sub hlimit).div_const 2
  convert hrecover using 1
  · ext n
    ring
  · ring_nf
end MetricCodes.Spherical.HigherHierarchy
