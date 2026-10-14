-- Prove2me | solution 1 for KerrBL.hasDerivAt_Sig_r
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T09:38:21.379899+00:00
-- url     : https://prove2.me/submissions/0471291e-2c65-4f82-ba76-aec0e4fd3efd

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

theorem solution (a r c : ℝ) : HasDerivAt (fun u => Sig a u c) (2*r) r := by
  unfold Sig
  refine (((hasDerivAt_id' r).fun_pow 2).fun_add (hasDerivAt_const (r) (a^(2:ℕ)*c^(2:ℕ)))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp
