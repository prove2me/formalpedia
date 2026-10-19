-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.sub_binWeight_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:46:04.160329+00:00
-- url     : https://prove2.me/submissions/ad2bfe84-a5fb-43f2-830e-0c5fa74ce54e

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SpectralBins.lean:L177-L194
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.sub_binWeight_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins

-- ---- from OAI.Probability.EntangledGames.SpectralBins ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_n u_ι

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open MeasureTheory Set
open scoped Interval

namespace ThresholdParallelRepetition.QuantumSampling

lemma sub_binWeight_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (s : ℝ) :
    a - binWeight a ε s ≤ ε*a := by
  unfold binWeight
  split_ifs with hap
  · have hf := Int.lt_floor_add_one (Real.log a/ε+s)
    have hm := mul_lt_mul_of_pos_left hf hε
    have he : ε*(Real.log a/ε+s) = Real.log a + ε*s := by field_simp
    have hex : Real.exp (Real.log a - ε) ≤ Real.exp (ε*((⌊Real.log a/ε+s⌋ : ℝ)-s)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_sub, Real.exp_log hap] at hex
    have hex' : (1-ε)*a ≤ a / Real.exp ε := by
      have hh := Real.add_one_le_exp (-ε)
      rw [Real.exp_neg] at hh
      have hmul := mul_le_mul_of_nonneg_right hh ha
      simpa only [neg_add_eq_sub, div_eq_mul_inv, mul_comm] using hmul
    linarith
  · have : a = 0 := le_antisymm (le_of_not_gt hap) ha
    simp [this]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open MeasureTheory Set
open scoped Interval


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.sub_binWeight_le := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.sub_binWeight_le
