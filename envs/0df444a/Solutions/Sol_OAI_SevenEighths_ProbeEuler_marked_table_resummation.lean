-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.marked_table_resummation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:54.980444+00:00
-- url     : https://prove2.me/submissions/a565a9ab-f1c3-47c2-8634-0a9759686b74

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
namespace OAI.SevenEighths.ProbeEuler
theorem _root_.solution (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert hgeo.mul_left (K * V ^ a) using 1 <;> try rfl
    funext m
    rw [pow_add]
    ring
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring
end OAI.SevenEighths.ProbeEuler
