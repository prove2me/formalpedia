-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_Phi_opening_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/c8f9c7ac-8103-445c-9391-376bee1450e5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_opening_entropy_slope
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_opening_eq

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
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (hr : 0 < r)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      Phi (openingAmbient a (η * t) (t ^ 2)) b < Phi a b := by
  let i : Fin r := ⟨0, hr⟩
  have ha : 0 < a 0 := by
    have hi := (h.stabilizer_pos i).trans (h.2 i).1
    simpa [i] using hi
  have hlog : 0 < Real.logb 2 ((1 + a 0) / a 0) := by
    apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    exact (lt_div_iff₀ ha).mpr (by linarith)
  have hnegative : -(η * Real.logb 2 ((1 + a 0) / a 0)) < 0 := by
    exact neg_neg_of_pos (mul_pos hη hlog)
  have hlimit := tendsto_opening_entropy_slope (η := η) ha
  have hevent := hlimit.eventually (gt_mem_nhds hnegative)
  filter_upwards [hevent, self_mem_nhdsWithin] with t ht (htpos : 0 < t)
  have hnegative' := (div_lt_iff₀ htpos).mp ht
  have hphi := Phi_opening_eq (b := b) hr hzero η t
  linarith
end MetricCodes.Spherical.HigherHierarchy
