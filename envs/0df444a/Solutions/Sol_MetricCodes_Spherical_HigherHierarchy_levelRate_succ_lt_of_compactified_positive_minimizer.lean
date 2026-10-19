-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_succ_lt_of_compactified_positive_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/28ab02ad-263d-4b2d-8ce4-ae8dd97b22b0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_nextLevel_strict_refinement

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r j : ℕ} {s c : ℝ}
    {a : Fin (j + 1) → ℝ} {b : Fin j → ℝ}
    (hj : j ≤ r) (hc : 0 < c) (hc' : c ≤ 1)
    (hdrop : c < 1 → j < r)
    (h : Interlacing a b) (hlast : 0 < a (Fin.last j))
    (hfeasible : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hmin : levelRate r s = Phi a b - Real.logb 2 c)
    (htransfer : ∀ {k j' : ℕ}
      (A : Fin (j' + 1) → ℝ) (B : Fin j' → ℝ),
      Interlacing A B →
      s < 1 - c ^ 2 * (1 - 2 * Gamma A B) →
      ((c = 1 ∧ j' ≤ k) ∨ (c < 1 ∧ j' + 1 ≤ k)) →
      levelRate k s ≤ Phi A B - Real.logb 2 c) :
    levelRate (r + 1) s < levelRate r s := by
  obtain ⟨A, B, hAB, hGamma, hPhi⟩ :=
    exists_nextLevel_strict_refinement h hlast
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hgap : s < 1 - c ^ 2 * (1 - 2 * Gamma A B) := by
    nlinarith
  have hlevels :
      (c = 1 ∧ j + 1 ≤ r + 1) ∨
        (c < 1 ∧ (j + 1) + 1 ≤ r + 1) := by
    rcases lt_or_eq_of_le hc' with hlt | rfl
    · have hjdrop := hdrop hlt
      exact Or.inr ⟨hlt, by omega⟩
    · exact Or.inl ⟨rfl, by omega⟩
  calc
    levelRate (r + 1) s ≤ Phi A B - Real.logb 2 c :=
      htransfer A B hAB hgap hlevels
    _ < Phi a b - Real.logb 2 c := by linarith
    _ = levelRate r s := hmin.symm
end MetricCodes.Spherical.HigherHierarchy
