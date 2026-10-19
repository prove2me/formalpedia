-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MeasurementTransport.supportInverse_commute
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:38:15.348217+00:00
-- url     : https://prove2.me/submissions/8030e581-c641-41c5-8674-90494daecb17

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/MeasurementTransport.lean:L55-L69
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MeasurementTransport.supportInverse_commute. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport

-- ---- from OAI.Probability.EntangledGames.MeasurementTransport ----
namespace OAI

universe u_n u_m u_A

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace ThresholdParallelRepetition.MeasurementTransport
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma supportInverse_commute {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T = T * supportInverse T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change cfc (fun t : ℝ => t⁻¹) T * T = T * cfc (fun t : ℝ => t⁻¹) T
  calc
    _ = cfc (fun t : ℝ => t⁻¹) T * cfc (fun t : ℝ => t) T := by rw [hid]
    _ = cfc (fun t : ℝ => t⁻¹ * t) T := by
      erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = cfc (fun t : ℝ => t * t⁻¹) T := by
      apply cfc_congr; intro t _; exact mul_comm _ _
    _ = cfc (fun t : ℝ => t) T * cfc (fun t : ℝ => t⁻¹) T := by
      erw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t⁻¹) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = _ := by rw [hid]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

variable {A : Type u_A} [Fintype A] [DecidableEq A]

end ThresholdParallelRepetition.MeasurementTransport

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MeasurementTransport
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.MeasurementTransport.supportInverse_commute.{u_n} := @_root_.OAI.ThresholdParallelRepetition.MeasurementTransport.supportInverse_commute.{u_n}
