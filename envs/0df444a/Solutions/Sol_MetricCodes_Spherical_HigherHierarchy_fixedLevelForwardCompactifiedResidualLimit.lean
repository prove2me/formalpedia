-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelForwardCompactifiedResidualLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/a2204e9a-5d1f-478e-863a-f5fdd50450cf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_Gamma_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_forward_residual_entropy_of_closure_sequence
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Gamma_of_compactified_suffix

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
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (r : ℕ) : FixedLevelForwardCompactifiedResidualLimit r := by
  intro C a b hinter hbound
  have hnegative : ∀ n, (-1 : ℝ) < 2 * Gamma (a n) (b n) := by
    intro n
    linarith [(hinter n).Gamma_nonneg]
  have herror : ∀ n : ℕ,
      Phi (a n) (b n) ≤ C + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith [hbound n]
  obtain ⟨L, X, Y, d, φ, k, j, hkj, q, A, B, c,
      hφ, hLnonneg, hLC, hX, hY, hXlim, hYlim,
      hthreshold, hnegativeφ, hPhilim, hd, hdlim,
      hpaired, hescape, hq, hAB, hprefix, hzero,
      hpositiveX, hpositiveY, hweak,
      hresidualPhi, hstieltjes, hc, hcpos, hcle, hdrop,
      hPhiidentity⟩ :=
    exists_forward_residual_entropy_of_closure_sequence
      (fun _ : ℕ => (-1 : ℝ)) a b
      (tendsto_const_nhds (x := (-1 : ℝ)))
      hinter hnegative herror
  have hGamma : Tendsto
      (fun n => Gamma (a (φ n)) (b (φ n)))
      atTop (nhds (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A B)) := by
    exact tendsto_Gamma_of_compactified_suffix
      hkj (fun n => a (φ n)) (fun n => b (φ n)) X Y d A B c
      (fun n => hinter (φ n)) hAB hX hXlim hYlim hdlim
      (fun i hi => (hprefix i hi).1)
      (fun i => (hpositiveX i).1)
      (fun i => (hpositiveY i).1)
      hstieltjes hc
  have hlevels : (c = 1 ∧ q ≤ r) ∨ (c < 1 ∧ q + 1 ≤ r) := by
    rcases hcle.lt_or_eq with hc_lt | hc_one
    · exact Or.inr ⟨hc_lt, by have hqr := hdrop hc_lt; omega⟩
    · exact Or.inl ⟨hc_one, by omega⟩
  refine ⟨q, c, A, B, φ, hφ, hcpos, hcle, hAB, hlevels, hGamma, ?_⟩
  simpa only [hPhiidentity] using hPhilim
end MetricCodes.Spherical.HigherHierarchy
