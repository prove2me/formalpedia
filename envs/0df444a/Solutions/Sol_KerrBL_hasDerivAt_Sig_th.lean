-- Prove2me | solution 1 for KerrBL.hasDerivAt_Sig_th
-- status  : ACCEPTED   (prove)
-- author  : @He Wang
-- created : 2026-09-09T09:38:56.125979+00:00
-- url     : https://prove2.me/submissions/c5aa68b5-85f5-4283-a3ed-a53db44f50e4

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

theorem solution (a r θ : ℝ) : HasDerivAt (fun θ => Sig a r (Real.cos θ)) (((-2))*Real.sin θ*Real.cos θ*a^(2:ℕ)) θ := by
  unfold Sig
  refine ((hasDerivAt_const (θ) (r^(2:ℕ))).fun_add ((hasDerivAt_const (θ) (a^(2:ℕ))).fun_mul ((Real.hasDerivAt_cos θ).fun_pow 2))).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | ring1 | (field_simp; ring1) | field_simp
