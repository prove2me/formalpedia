-- Prove2me | solution 1 for KerrBL.hasDerivAt_Del_r
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T09:39:39.518192+00:00
-- url     : https://prove2.me/submissions/977565f8-1d27-488f-bb3a-b79c2d544111

import Definitions.Def_KerrBL_Kerr_Metric
import Definitions.Def_KerrBL_CoordGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Constructions
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open KerrBL Filter Topology

theorem solution (M a r : ℝ) : HasDerivAt (fun u => Del M a u) (((-2))*M + 2*r) r := by
  unfold Del
  refine (((hasDerivAt_const (r) (a^(2:ℕ))).fun_add ((hasDerivAt_id' r).fun_pow 2)).fun_sub ((hasDerivAt_const (r) ((2*M))).fun_mul (hasDerivAt_id' r))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp
