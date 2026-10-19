-- Prove2me | solution 1 for MetricCodes.Hamming.binaryRate_le_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/0b6ecb60-67bb-457a-b777-37ada4303313

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_codeLogRate_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ r : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds r))
    (hbound : ∀ᶠ n : ℕ in atTop,
      Real.logb 2
        (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) ≤ u n) :
    binaryRate δ ≤ r := by
  let w : ℕ → ℝ := fun n =>
    Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ)
  have hlower : atTop.IsBoundedUnder (· ≥ ·) w :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (codeLogRate_nonneg δ))
  have hcob : atTop.IsCoboundedUnder (· ≤ ·) w :=
    hlower.isCoboundedUnder_le
  have hcomparison : Filter.limsup w atTop ≤ Filter.limsup u atTop :=
    Filter.limsup_le_limsup hbound hcob hu.isBoundedUnder_le
  change Filter.limsup w atTop ≤ r
  exact hcomparison.trans_eq hu.limsup_eq
end MetricCodes.Hamming
