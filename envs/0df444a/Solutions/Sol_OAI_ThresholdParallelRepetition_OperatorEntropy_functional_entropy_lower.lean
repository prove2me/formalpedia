-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.OperatorEntropy.functional_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:12:09.425912+00:00
-- url     : https://prove2.me/submissions/3fbcab8d-a40d-4e6e-ae7d-583c9e557b7b

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/RelativeEntropy.lean:L159-L185
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.OperatorEntropy.functional_entropy_lower. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_ScalarEntropy_negMulLog_subprob

-- ---- from OAI.Probability.EntangledGames.SpectralEntropy ----
namespace OAI

universe u_n u_α u_m u_p u_r u_J

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Topology Matrix.Norms.Elementwise
open Matrix MeasureTheory Set
namespace ThresholdParallelRepetition.Resolvent
variable {n : Type u_n} [Fintype n] [DecidableEq n]

attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.matrixContinuousENorm
attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.matrixPreorder
attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.matrixClosedIci
lemma spectralLinear_apply (U : Matrix n n ℂ) (v : n → ℝ) :
    spectralLinear U v = U * diagonal (fun i => (v i : ℂ)) * Uᴴ := rfl

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]
attribute [local instance] OAI.ThresholdParallelRepetition.Resolvent.rectContinuousENorm
end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.Resolvent

end
end
end
end

end OAI

-- ---- from OAI.Probability.EntangledGames.RelativeEntropy ----
namespace OAI

universe u_ι u_α u_β u_n u_m

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ThresholdParallelRepetition
namespace ScalarEntropy

open FiniteProbability
variable {α : Type u_α} {β : Type u_β} [Fintype α] [Fintype β]

end ScalarEntropy
namespace OperatorEntropy
open Resolvent QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma spectralLinear_sum (U : Matrix n n ℂ) (v : n → ℝ) :
    spectralLinear U v = ∑ i, v i • spectralLinear U (Pi.single i 1) := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul]

lemma spectralLinear_single_pos (U : Matrix n n ℂ) (i : n) :
    (spectralLinear U (Pi.single i 1)).PosSemidef := by
  rw [spectralLinear_apply]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro j
  simp only [Pi.single_apply]
  split_ifs <;> simp

lemma spectralLinear_one (U : Matrix n n ℂ) (hU : U*Uᴴ=1) :
    spectralLinear U (fun _ => 1) = 1 := by
  simp [spectralLinear_apply, Matrix.diagonal_one, hU]

lemma functional_entropy_lower (Φ : Matrix n n ℂ →ₗ[ℝ] ℝ)
    (hΦ : ∀ A : Matrix n n ℂ, A.PosSemidef → 0 ≤ Φ A)
    (hmass : Φ 1 ≤ 1) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    -Φ (effectEntropy A) ≤ Real.negMulLog (Φ A) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let w : n → ℝ := fun i => Φ (spectralLinear U (Pi.single i 1))
  have hw : ∀ i, 0 ≤ w i := fun i => hΦ _ (spectralLinear_single_pos U i)
  have hU : U*Uᴴ=1 := Unitary.mul_star_self_of_mem hA.isHermitian.eigenvectorUnitary.property
  have hone : ∑ i, w i = Φ 1 := by
    rw [← spectralLinear_one U hU, spectralLinear_sum]
    simp only [map_sum, map_smul, smul_eq_mul, one_mul, w]
  have heval (f : ℝ → ℝ) : Φ (cfc f A) = ∑ i, w i*f (hA.isHermitian.eigenvalues i) := by
    rw [cfc_eq_spectralLinear hA.isHermitian, spectralLinear_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hid : Φ A = ∑ i, w i*hA.isHermitian.eigenvalues i := by
    have h := heval id
    erw [cfc_id' ℝ A hA.isHermitian] at h
    exact h
  have hh := ScalarEntropy.negMulLog_subprob w hA.isHermitian.eigenvalues hw
    (hone.trans_le hmass) hA.eigenvalues_nonneg
  rw [← hid] at hh
  rw [effectEntropy, heval]
  convert hh using 1
  simp only [Real.negMulLog_def, mul_neg, neg_mul, Finset.sum_neg_distrib]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

end OperatorEntropy
end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.OperatorEntropy
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open Resolvent QuantumSampling


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.OperatorEntropy.functional_entropy_lower.{u_n} := @_root_.OAI.ThresholdParallelRepetition.OperatorEntropy.functional_entropy_lower.{u_n}
