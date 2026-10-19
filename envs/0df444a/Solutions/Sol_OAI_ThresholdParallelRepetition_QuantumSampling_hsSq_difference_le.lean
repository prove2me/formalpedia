-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:02:37.234874+00:00
-- url     : https://prove2.me/submissions/3896847c-7234-4a54-930d-224f774aa258

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CorrelatedSampling.lean:L32-L45
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_difference_le. The node keeps its source
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
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling

-- ---- from OAI.Probability.EntangledGames.HilbertSchmidt ----
namespace OAI

universe u_m u_n u_p u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.CorrelatedSampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_m u_n u_A u_B u_p u_ι

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Norm
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma norm_eq_sqrt_hsSq (M : Matrix m n ℂ) : ‖M‖ = Real.sqrt (hsSq M) := by
  simp only [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, hsSq,
    Real.rpow_two, Complex.sq_norm]
lemma hsSq_le_one_norm {M : Matrix m n ℂ} (hM : hsSq M ≤ 1) : ‖M‖ ≤ 1 := by
  rw [norm_eq_sqrt_hsSq]
  exact Real.sqrt_le_one.mpr hM
lemma hsSq_difference_le (M N : Matrix m n ℂ) (hM : hsSq M ≤ 1) (hN : hsSq N ≤ 1) :
    hsSq M - hsSq N ≤ 2 * Real.sqrt (hsSq (M-N)) := by
  have hm := hsSq_le_one_norm hM
  have hn := hsSq_le_one_norm hN
  have hd := norm_sub_norm_le M N
  have h0 := norm_nonneg M
  have h1 := norm_nonneg N
  have h2 := norm_nonneg (M-N)
  have hh := mul_le_mul_of_nonneg_left hd (add_nonneg h0 h1)
  have hh' := mul_le_mul_of_nonneg_right (add_le_add hm hn) h2
  rw [norm_eq_sqrt_hsSq M, norm_eq_sqrt_hsSq N, norm_eq_sqrt_hsSq (M-N)] at hh hh'
  have hsqM := Real.sq_sqrt (hsSq_nonneg M)
  have hsqN := Real.sq_sqrt (hsSq_nonneg N)
  nlinarith
end Norm

section WinEffect
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]
end WinEffect

section Blocks
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype p] [Fintype ι]
end Blocks

section Resource
variable {n : Type u_n} [Fintype n] [DecidableEq n]
end Resource

end ThresholdParallelRepetition.QuantumSampling

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
open scoped Interval
open scoped Kronecker
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
open scoped Matrix.Norms.Frobenius


theorem solution.{u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_difference_le.{u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_difference_le.{u_m,u_n}
