-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference.shiftedRowGap_sub_shiftedRowGap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/2a3ff26e-7fe1-43c1-8c35-38cc6500f2c7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
theorem _root_.solution
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (a i j : Fin (r + 1)) (hai : a < i) (hij : i < j)
    (hji : lam j ≤ lam i) (hia : lam i ≤ lam a) :
    shiftedRowGap lam j a - shiftedRowGap lam i a =
      shiftedRowGap lam j i + 1 := by
  have hja : lam j ≤ lam a := hji.trans hia
  have hja_index : 1 ≤ j.val - a.val := by omega
  have hia_index : 1 ≤ i.val - a.val := by omega
  have hji_index : 1 ≤ j.val - i.val := by omega
  unfold shiftedRowGap
  rw [Nat.cast_sub hja, Nat.cast_sub hia, Nat.cast_sub hji,
    Nat.cast_sub hja_index, Nat.cast_sub hia_index,
    Nat.cast_sub hji_index,
    Nat.cast_sub (by omega : a.val ≤ j.val),
    Nat.cast_sub (by omega : a.val ≤ i.val),
    Nat.cast_sub (by omega : i.val ≤ j.val)]
  norm_num
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
