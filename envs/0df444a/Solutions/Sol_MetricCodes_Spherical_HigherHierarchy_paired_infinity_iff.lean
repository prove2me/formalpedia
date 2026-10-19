-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.paired_infinity_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/e2d3f7c1-d1f9-400b-8645-8a99fb53e320

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyTuple_limit_weak_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_WeakInterlacing_ambient_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_stabilizer_tendsto_atTop_of_ambient

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
theorem _root_.solution
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ} {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i) :
    ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0 := by
  intro i
  constructor
  · intro hzero
    have hatop : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop :=
      tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
        (fun n => (h (φ n)).ambient_nonneg i.castSucc)
        (hzero ▸ hA i.castSucc)
    have hbtop := paired_stabilizer_tendsto_atTop_of_ambient
      h hPhi i hatop
    have hone : Tendsto (fun n => 1 + b (φ n) i) atTop atTop :=
      tendsto_atTop_add_const_left atTop 1 hbtop
    have hzero' : Tendsto
        (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
          atTop (nhds 0) := by
      exact tendsto_inv_atTop_zero.comp hone
    exact tendsto_nhds_unique (hB i) hzero'
  · intro hzero
    have hweak := compactifiedHierarchyTuple_limit_weak_interlacing
      h hA hB i
    exact le_antisymm (hzero ▸ hweak.1) (hAnonneg i.castSucc)
end MetricCodes.Spherical.HigherHierarchy
