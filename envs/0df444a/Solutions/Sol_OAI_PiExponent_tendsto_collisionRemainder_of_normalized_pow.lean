-- Prove2me | solution 1 for OAI.PiExponent.tendsto_collisionRemainder_of_normalized_pow
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-11T21:03:33.82965+00:00
-- url     : https://prove2.me/submissions/f31fb318-a908-4905-beef-f1f9d8d716d3

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_tendsto_log_div_of_normalized_pow

namespace OAI.PiExponent

open Filter Topology
open scoped BigOperators

theorem tendsto_log_add_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) (C : ℝ) :
    Tendsto (fun H : ℝ => (Real.log (f H) + C) / H) atTop (𝓝 0) := by
  have h := (tendsto_log_div_of_normalized_pow hf hL).add
    (tendsto_id.const_div_atTop C)
  simpa only [add_zero, add_div, id_eq] using h

end OAI.PiExponent

open scoped BigOperators Topology
open Filter
open OAI.PiExponent

theorem solution {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  convert tendsto_log_add_div_of_normalized_pow hM hL
    (Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio)) using 1
  funext H
  unfold Collision.collisionRemainder
  congr 1
  ring
