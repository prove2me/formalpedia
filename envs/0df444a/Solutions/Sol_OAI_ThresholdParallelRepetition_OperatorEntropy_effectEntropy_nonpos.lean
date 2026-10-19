-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.OperatorEntropy.effectEntropy_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:10:34.079657+00:00
-- url     : https://prove2.me/submissions/c76ad87f-2fc8-4b70-8ad7-41e867614acb

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/RelativeEntropy.lean:L124-L136
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.OperatorEntropy.effectEntropy_nonpos. The node keeps its source
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
end ThresholdParallelRepetition.Resolvent

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma eigenvalues_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (i : n) : hA.isHermitian.eigenvalues i ≤ 1 := by
  have h : cfc (fun t : ℝ => t) A ≤ cfc (fun _ : ℝ => (1 : ℝ)) A := by
    erw [cfc_id' ℝ A hA.isHermitian, cfc_const (1 : ℝ) A hA.isHermitian,
      map_one]
    exact hA1
  exact (cfc_le_iff (fun t : ℝ => t) (fun _ : ℝ => (1 : ℝ)) A
    (ha := hA.isHermitian)).mp h _ (hA.isHermitian.eigenvalues_mem_spectrum_real i)

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

lemma effectEntropy_nonpos {A : Matrix n n ℂ} (hA : A.PosSemidef) (hA1 : A ≤ 1) :
    effectEntropy A ≤ 0 := by
  rw [effectEntropy]
  have hz : cfc (fun _ : ℝ => (0 : ℝ)) A = 0 := by simp
  rw [← hz]
  apply (cfc_le_iff _ _ A (hf := Real.continuous_mul_log.continuousOn) (ha := hA.isHermitian)).mpr
  intro t ht
  have ht0 := spectrum_nonneg hA ht
  have ht1 : t ≤ 1 := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
    obtain ⟨i,rfl⟩ := ht
    exact eigenvalues_le_one hA hA1 i
  exact Real.mul_log_nonpos ht0 ht1

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


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.OperatorEntropy.effectEntropy_nonpos.{u_n} := @_root_.OAI.ThresholdParallelRepetition.OperatorEntropy.effectEntropy_nonpos.{u_n}
