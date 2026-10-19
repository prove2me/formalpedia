-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_spectral_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:44:30.859624+00:00
-- url     : https://prove2.me/submissions/372ee753-68d9-428a-834f-41deb1b74fca

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/HilbertSchmidt.lean:L55-L91
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_spectral_mixed. The node keeps its source
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

lemma hsSq_spectral_mixed [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    hsSq (cfc f A - cfc g B) =
      ∑ i, ∑ j, (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hB.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.eigenvectorUnitary
  have hUU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  have hUU' : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have hVV : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  have hVV' : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  have hf : cfc f A = U * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ := by
    erw [hA.cfc_eq]
    rfl
  have hg : cfc g B = V * Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ)) * Vᴴ := by
    erw [hB.cfc_eq]
    rfl
  have hmixed : Uᴴ * (cfc f A - cfc g B) * V =
      Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * (Uᴴ * V) -
      (Uᴴ * V) * Matrix.diagonal (fun i => (g (hB.eigenvalues i) : ℂ)) := by
    rw [hf, hg, Matrix.mul_sub, Matrix.sub_mul]
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    simp only [Matrix.mul_assoc, hVV', Matrix.mul_one]
  rw [← hsSq_mul_left (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hUU)
      (cfc f A - cfc g B),
    ← hsSq_mul_right hVV (Uᴴ * (cfc f A - cfc g B)), hmixed]
  unfold hsSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_comm ((Uᴴ * V) i j), ← sub_mul, ← Complex.ofReal_sub, Complex.normSq_mul,
    Complex.normSq_ofReal]
  simp only [pow_two]
  rfl

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
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_spectral_mixed.{u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.hsSq_spectral_mixed.{u_n}
