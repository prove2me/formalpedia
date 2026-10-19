-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.paired_stabilizer_tendsto_atTop_of_ambient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/573c8e15-fa42-4cc5-80c8-650dd06e477d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_entropy_gap_le_Phi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_shifted_degree_ratio_le_rpow_of_entropy_gap_le

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
    {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (i : Fin r)
    (ha : Tendsto (fun n => a (φ n) i.castSucc) atTop atTop) :
    Tendsto (fun n => b (φ n) i) atTop atTop := by
  let D : ℝ := (2 : ℝ) ^ (C + 1 / Real.log 2)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  have hgap : ∀ n,
      MetricCodes.sphericalEntropy (a (φ n) i.castSucc) -
        MetricCodes.sphericalEntropy (b (φ n) i) ≤ C :=
    fun n =>
      (CompactificationEntropy.entropy_gap_le_Phi (h (φ n)) i).trans
        (hPhi (φ n))
  have hbound : ∀ n,
      a (φ n) i.castSucc / D - 1 ≤ b (φ n) i := by
    intro n
    have hratio :=
      CompactificationEntropy.shifted_degree_ratio_le_rpow_of_entropy_gap_le
        ((h (φ n)).stabilizer_pos i)
        ((h (φ n)).2 i).1.le (hgap n)
    change (1 + a (φ n) i.castSucc) /
      (1 + b (φ n) i) ≤ D at hratio
    have hmul : 1 + a (φ n) i.castSucc ≤
        D * (1 + b (φ n) i) :=
      (div_le_iff₀
        (by linarith [(h (φ n)).stabilizer_pos i])).mp hratio
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have hleft : Tendsto
      (fun n => a (φ n) i.castSucc / D - 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-1)
      (ha.atTop_div_const hD) using 1
    ext n
    ring
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall hbound) hleft
end MetricCodes.Spherical.HigherHierarchy
