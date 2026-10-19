-- Prove2me | solution 1 for MetricCodes.Hamming.ceil_distance_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/04673372-e366-40cb-91c1-07d546c2044d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) :
    0 < Nat.ceil (δ * (n : ℝ)) := by
  apply Nat.ceil_pos.mpr
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos hδ hnreal
end MetricCodes.Hamming
