-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_compactified_positive_levelRate_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/9f872bbf-ad69-4f12-8a43-83d797332865

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Gamma_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_sameLevel_opening_strict_refinement
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_levelRate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_compactified_datum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_classicalThreshold_entropy_lt_neg_logb_of_compactified_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_zero_eq_classical
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_levelRate_minimizer

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
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ (j : ℕ) (c : ℝ)
      (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ),
      j ≤ r ∧ 0 < c ∧ c ≤ 1 ∧ (c < 1 → j < r) ∧
      Interlacing a b ∧ 0 < a (Fin.last j) ∧
      s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b) ∧
      levelRate r s = Phi a b - Real.logb 2 c := by
  obtain ⟨j, c, a, b, hc, hc', h, hlevels, hfeasible, hmin⟩ :=
    exists_compactified_levelRate_minimizer hs hs'
  have hj : j ≤ r := by
    rcases hlevels with ⟨_, hj⟩ | ⟨_, hj⟩ <;> omega
  have hdrop : c < 1 → j < r := by
    intro hclt
    rcases hlevels with ⟨hcone, _⟩ | ⟨_, hj⟩
    · linarith
    · omega
  have hlast : 0 < a (Fin.last j) := by
    by_contra hnot
    have hzero : a (Fin.last j) = 0 :=
      le_antisymm (le_of_not_gt hnot) (h.ambient_nonneg (Fin.last j))
    cases j with
    | zero =>
        have ha : a 0 = 0 := by simpa using hzero
        have hGamma : Gamma a b = 0 := by
          simp [Gamma_zero, ha, spectralAtom, quadraticCoordinate]
        have hPhi : Phi a b = 0 := by
          simp [Phi_zero, ha]
        have hscaled : s ≤ 1 - c ^ 2 := by
          rw [hGamma] at hfeasible
          nlinarith
        have hclassical :=
          classicalThreshold_entropy_lt_neg_logb_of_compactified_zero
            hs hs' hc hscaled
        have hupper : levelRate r s ≤
            MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
          calc
            levelRate r s ≤ levelRate 0 s :=
              levelRate_le_levelRate_zero hs hs'
            _ = MetricCodes.sphericalEntropy
                  (MetricCodes.classicalThreshold s) :=
              levelRate_zero_eq_classical hs.le hs'
        rw [hPhi] at hmin
        linarith
    | succ j =>
        obtain ⟨A, _, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos j) h hzero
        have hstrict :
            s < 1 - c ^ 2 * (1 - 2 * Gamma A b) := by
          nlinarith [sq_pos_of_pos hc]
        have hupper := levelRate_le_compactified_datum
          hs hs' hc A b hA hstrict hlevels
        linarith
  exact ⟨j, c, a, b, hj, hc, hc', hdrop, h,
    hlast, hfeasible, hmin⟩
end MetricCodes.Spherical.HigherHierarchy
