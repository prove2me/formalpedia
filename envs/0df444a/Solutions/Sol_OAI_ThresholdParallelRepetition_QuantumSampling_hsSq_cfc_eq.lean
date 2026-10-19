-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_cfc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:47:22.642141+00:00
-- url     : https://prove2.me/submissions/ae52e301-64c5-4b6b-816c-b7b48b5e7865

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SpectralBins.lean:L215-L229
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_cfc_eq. The node keeps its source
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

lemma hsSq_conjTranspose (M : Matrix m n ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

lemma hsSq_eq_trace (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, hsSq]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [Complex.mul_re, Complex.normSq_apply]

lemma hsSq_mul_left {U : Matrix m m ℂ} [DecidableEq m] (hU : Uᴴ * U = 1)
    (M : Matrix m n ℂ) : hsSq (U * M) = hsSq M := by
  rw [hsSq_eq_trace, Matrix.conjTranspose_mul]
  rw [show (Mᴴ * Uᴴ) * (U * M) = Mᴴ * (Uᴴ * U) * M by simp only [Matrix.mul_assoc],
    hU, Matrix.mul_one, ← hsSq_eq_trace]

lemma hsSq_mul_right {U : Matrix n n ℂ} [DecidableEq n] (hU : U * Uᴴ = 1)
    (M : Matrix m n ℂ) : hsSq (M * U) = hsSq M := by
  rw [← hsSq_conjTranspose, Matrix.conjTranspose_mul]
  rw [hsSq_mul_left (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU),
    hsSq_conjTranspose]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

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

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma hsSq_cfc_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    hsSq (cfc f A) = ∑ i, (f (hA.eigenvalues i))^2 := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have he : cfc f A = U * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ := by
    erw [hA.cfc_eq]; rfl
  rw [he, hsSq_mul_right (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU), hsSq_mul_left hU]
  unfold hsSq
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [Complex.normSq_ofReal, pow_two]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), Complex.normSq_zero]
  · simp

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
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_cfc_eq.{u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_cfc_eq.{u_n}
