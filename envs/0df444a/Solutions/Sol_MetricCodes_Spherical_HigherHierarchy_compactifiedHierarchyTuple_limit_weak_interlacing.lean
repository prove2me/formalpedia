-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedHierarchyTuple_limit_weak_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/b325b164-37e1-4f2c-a714-5d7d847515fa

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyCoordinate_antitone

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
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ} {φ : ℕ → ℕ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hA : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
      atTop (nhds (B i))) :
    ∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ := by
  intro i
  constructor
  · have hlim := (hA i.castSucc).sub (hB i)
    have hle : A i.castSucc - B i ≤ 0 := by
      apply le_of_tendsto hlim
      exact Filter.Eventually.of_forall fun k => sub_nonpos.mpr
        (compactifiedHierarchyCoordinate_antitone
          ((h (φ k)).stabilizer_pos i).le
          ((h (φ k)).ambient_nonneg i.castSucc)
          ((h (φ k)).2 i).1.le)
    linarith
  · have hlim := (hB i).sub (hA i.succ)
    have hle : B i - A i.succ ≤ 0 := by
      apply le_of_tendsto hlim
      exact Filter.Eventually.of_forall fun k => sub_nonpos.mpr
        (compactifiedHierarchyCoordinate_antitone
          ((h (φ k)).ambient_nonneg i.succ)
          ((h (φ k)).stabilizer_pos i).le
          ((h (φ k)).2 i).2.le)
    linarith
end MetricCodes.Spherical.HigherHierarchy
