-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.polar_gram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:50:34.55875+00:00
-- url     : https://prove2.me/submissions/b3675a6d-e82b-4263-98a6-b9edbb18d3fd

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CoherentFilters.lean:L55-L69
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.polar_gram. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_supportInverse_commute

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

lemma rightAbs_pos (M : Matrix m n ℂ) : (rightAbs M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
lemma rightAbs_sq (M : Matrix m n ℂ) : rightAbs M * rightAbs M = Mᴴ*M :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg

lemma polar_gram (M : Matrix m n ℂ) :
    (polar M)ᴴ * polar M = supportInverse (rightAbs M) * rightAbs M := by
  let A := rightAbs M
  let D := supportInverse A
  have hA : A.IsHermitian := (rightAbs_pos M).isHermitian
  have hD : Dᴴ = D := (supportInverse_isHermitian A).eq
  change (M*D)ᴴ*(M*D) = D*A
  rw [Matrix.conjTranspose_mul, hD]
  calc
    _ = D*(Mᴴ*M)*D := by simp only [Matrix.mul_assoc]
    _ = D*(A*A)*D := by rw [rightAbs_sq]
    _ = D*A*(A*D) := by simp only [Matrix.mul_assoc]
    _ = D*A*(D*A) := by rw [show A*D=D*A from (supportInverse_commute hA).symm]
    _ = (D*A*D)*A := by simp only [Matrix.mul_assoc]
    _ = D*A := by rw [supportInverse_mul_self_mul hA]

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

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open ThresholdParallelRepetition.MeasurementTransport


theorem solution.{u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.polar_gram.{u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.polar_gram.{u_m,u_n}
