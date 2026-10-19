-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_bounded_hierarchy_entropy_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/8e6a4785-5bdd-4f02-b445-68ebd427f9ee

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_Phi_nonneg_refinement

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
theorem _root_.solution {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hbound : ∀ k, Phi (a k) (b k) ≤ C) :
    ∃ (L : ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ L ∈ Set.Icc (0 : ℝ) C ∧
      Tendsto (fun k => Phi (a (φ k)) (b (φ k)))
        atTop (nhds L) := by
  obtain ⟨L, hL, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).tendsto_subseq
      (fun k => ⟨(h k).Phi_nonneg_refinement, hbound k⟩)
  exact ⟨L, φ, hφ, hL, hlim⟩
end MetricCodes.Spherical.HigherHierarchy
