-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_compactified_bounded_hierarchy_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/f23d4dc9-4568-46b7-8e32-c8ff7eb3badf

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactifiedHierarchyTuple_subsequence
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyTuple_limit_weak_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyTuple_terminal_limit_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_bounded_hierarchy_entropy_subsequence

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
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (φ : ℕ → ℕ),
      StrictMono φ ∧ L ∈ Set.Icc (0 : ℝ) C ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
        atTop (nhds (B i))) ∧
      (∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ) ∧
      0 < A (Fin.last r) ∧
      Tendsto (fun k => Phi (a (φ k)) (b (φ k)))
        atTop (nhds L) := by
  obtain ⟨L, ψ, hψ, hL, hlim⟩ :=
    exists_bounded_hierarchy_entropy_subsequence a b h hbound
  obtain ⟨A, B, χ, hχ, hA, hB, ha, hb⟩ :=
    exists_compactifiedHierarchyTuple_subsequence
      (fun k => a (ψ k)) (fun k => b (ψ k))
      (fun k => h (ψ k))
  let φ : ℕ → ℕ := ψ ∘ χ
  have hφ : StrictMono φ := hψ.comp hχ
  have ha' : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
      atTop (nhds (A i)) := by
    intro i
    exact ha i
  have hb' : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
      atTop (nhds (B i)) := by
    intro i
    exact hb i
  refine ⟨L, A, B, φ, hφ, hL, hA, hB, ha', hb',
    compactifiedHierarchyTuple_limit_weak_interlacing h ha' hb',
    compactifiedHierarchyTuple_terminal_limit_pos h hbound
      (ha' (Fin.last r)), ?_⟩
  exact hlim.comp hχ.tendsto_atTop
end MetricCodes.Spherical.HigherHierarchy
