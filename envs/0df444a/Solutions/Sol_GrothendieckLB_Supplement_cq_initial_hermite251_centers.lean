-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_initial_hermite251_centers
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:56:08.437612+00:00
-- url     : https://prove2.me/submissions/3bb829e6-0968-4ade-b8ee-4be3c56efadd

import Definitions.Def_GrothendieckLB_Supplement_cqInitialHermite251
open CQInitial251
set_option Elab.async false
set_option maxRecDepth 150000
set_option exponentiation.threshold 50000
set_option maxHeartbeats 300000000

private theorem checked_e0 : correctProduct .e0 false := by decide +kernel
private theorem checked_e2 : correctProduct .e2 false := by decide +kernel
private theorem checked_e4 : correctProduct .e4 false := by decide +kernel

theorem solution : ∀ a : Axis, correctProduct a false := by
  intro a
  cases a with
  | e0 => exact checked_e0
  | e2 => exact checked_e2
  | e4 => exact checked_e4
