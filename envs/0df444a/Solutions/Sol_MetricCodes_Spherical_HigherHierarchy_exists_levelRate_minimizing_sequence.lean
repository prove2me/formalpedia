-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_levelRate_minimizing_sequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/4f6d9334-883b-445d-a7f8-52b7dacc11f9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_bddBelow

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ} {s : ℝ}
    (hne : (levelRateSet r s).Nonempty) :
    ∃ (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ),
      (∀ k, Interlacing (a k) (b k) ∧ s < 2 * Gamma (a k) (b k)) ∧
      Antitone (fun k => Phi (a k) (b k)) ∧
      Tendsto (fun k => Phi (a k) (b k)) atTop (nhds (levelRate r s)) := by
  obtain ⟨z, hanti, hlim, hz⟩ :=
    exists_seq_tendsto_sInf hne (levelRateSet_bddBelow r s)
  have hdata : ∀ k : ℕ,
      ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
        Interlacing a b ∧ s < 2 * Gamma a b ∧ z k = Phi a b := hz
  choose a b hinter hgap heq using hdata
  refine ⟨a, b, fun k => ⟨hinter k, hgap k⟩, ?_, ?_⟩
  · simpa only [← heq] using hanti
  · simpa only [levelRate, ← heq] using hlim
end MetricCodes.Spherical.HigherHierarchy
