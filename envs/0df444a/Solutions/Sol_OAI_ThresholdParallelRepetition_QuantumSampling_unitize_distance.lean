-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.unitize_distance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:27:18.521876+00:00
-- url     : https://prove2.me/submissions/085e600c-bcc6-4aeb-b1bf-cb9c58dbda1d

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/BlockStates.lean:L93-L106
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.unitize_distance. The node keeps its source
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
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates

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

lemma hsSq_zero : hsSq (0 : Matrix m n ℂ) = 0 := by simp [hsSq]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.CoherentFilters ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_m u_n u_p u_ι u_q

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open ThresholdParallelRepetition.MeasurementTransport
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} [Fintype m] [Fintype n] [Fintype p]

lemma hsSq_neg (M : Matrix m n ℂ) : hsSq (-M) = hsSq M := by
  simp [hsSq, Complex.normSq_neg]
lemma hsSq_smul (r : ℝ) (M : Matrix m n ℂ) : hsSq (r • M) = r^2*hsSq M := by
  simp only [hsSq, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  congr 1
  ring
variable [DecidableEq m]
end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
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

-- ---- from OAI.Probability.EntangledGames.BlockStates ----
namespace OAI

universe u_m u_n u_R u_A u_B u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
section Blocks
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
variable [DecidableEq m]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq n]
end Blocks

section Normalization
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma hsSq_eq_zero_iff (C : Matrix m n ℂ) : hsSq C = 0 ↔ C = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [norm_eq_sqrt_hsSq, h, Real.sqrt_zero]
  · rintro rfl; exact hsSq_zero

lemma unitize_distance (C D : Matrix m n ℂ) (hD : hsSq D = 1) :
    hsSq (C-unitize C D) = (Real.sqrt (hsSq C)-1)^2 := by
  unfold unitize
  split_ifs with h
  · have hz := (hsSq_eq_zero_iff C).mp h
    simp only [hz, hsSq_zero, Real.sqrt_zero, zero_sub, hsSq_neg, hD]
    norm_num
  · have hs : Real.sqrt (hsSq C) ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne (hsSq_nonneg C) (Ne.symm h))).ne'
    have he : C - (Real.sqrt (hsSq C))⁻¹ • C = (1-(Real.sqrt (hsSq C))⁻¹) • C := by
      rw [sub_smul, one_smul]
    rw [he, hsSq_smul]
    calc
      _ = (1-(Real.sqrt (hsSq C))⁻¹)^2 * (Real.sqrt (hsSq C))^2 := by rw [Real.sq_sqrt (hsSq_nonneg C)]
      _ = _ := by field_simp

end Normalization

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A] [Fintype B]
end Payoff
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B]
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law
section Stack
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
end Stack

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped Matrix.Norms.Frobenius


theorem solution.{u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.unitize_distance.{u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.unitize_distance.{u_m,u_n}
