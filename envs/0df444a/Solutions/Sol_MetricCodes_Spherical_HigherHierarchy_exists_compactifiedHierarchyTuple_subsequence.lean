-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_compactifiedHierarchyTuple_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/c469c4b9-4737-4311-a733-294eb54630e7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyTuple_mem_cube
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_isCompact_hierarchyCompactCube

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
    (h : ∀ k, Interlacing (a k) (b k)) :
    ∃ (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
        atTop (nhds (B i))) := by
  obtain ⟨z, hz, φ, hmono, hlim⟩ :=
    (isCompact_hierarchyCompactCube r).tendsto_subseq
      (fun k => compactifiedHierarchyTuple_mem_cube (h k))
  refine ⟨fun i => z (Sum.inl i), fun i => z (Sum.inr i), φ,
    hmono, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hz (Sum.inl i) (Set.mem_univ _)
  · intro i
    exact hz (Sum.inr i) (Set.mem_univ _)
  · intro i
    have hi := (tendsto_pi_nhds.mp hlim) (Sum.inl i)
    exact hi
  · intro i
    have hi := (tendsto_pi_nhds.mp hlim) (Sum.inr i)
    exact hi
end MetricCodes.Spherical.HigherHierarchy
