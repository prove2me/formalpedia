-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.filter_mass_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:57:43.483223+00:00
-- url     : https://prove2.me/submissions/eeeb84af-b362-4294-94b8-22bcc097683c

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SamplingStrategy.lean:L327-L343
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.filter_mass_bounds. The node keeps its source
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

lemma eval_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    eval C (Kᴴ*A*K) (Lᴴ*B*L) = eval (K*C*Lᵀ) A B := by
  simp only [eval_eq_trace, Matrix.conjTranspose_mul, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose,
    Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

lemma prob_pullback (C : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (A : Matrix p p ℂ) (B : Matrix q q ℂ) :
    prob C (Kᴴ*A*K) (Lᴴ*B*L) = prob (K*C*Lᵀ) A B := by
  simp only [prob, eval_pullback]

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI

-- ---- from OAI.Probability.EntangledGames.SamplingStrategy ----
namespace OAI

universe u_n u_A u_m u_ι u_p u_q u_B

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise
open scoped Interval
open scoped Kronecker

noncomputable section
namespace ThresholdParallelRepetition.QuantumSampling

variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A]

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]

end Payoff

section FilterMass
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

omit [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
lemma prob_sub_left (C : Matrix m n ℂ) (A A' : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob C (A-A') B = prob C A B - prob C A' B := by
  simp only [prob, eval_eq_trace, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
omit [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q] in
lemma prob_sub_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B-B') = prob C A B - prob C A B' := by
  simp only [prob, eval_eq_trace, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

omit [DecidableEq n] [DecidableEq q] in
lemma prob_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (Kᴴ*K) (Lᴴ*L) = hsSq (K*D*Lᵀ) := by
  simpa only [Matrix.mul_one, prob_one] using prob_pullback D K L (1 : Matrix m m ℂ) (1 : Matrix p p ℂ)
omit [Fintype p] [DecidableEq p] [DecidableEq n] in
lemma prob_left_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) :
    prob D (Kᴴ*K) 1 = hsSq (K*D) := by
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] using
    prob_gram D K (1 : Matrix q q ℂ)
omit [Fintype m] [DecidableEq m] [DecidableEq q] in
lemma prob_right_gram (D : Matrix n q ℂ) (L : Matrix p q ℂ) :
    prob D 1 (Lᴴ*L) = hsSq (D*Lᵀ) := by
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul] using
    prob_gram D (1 : Matrix n n ℂ) L

lemma filter_mass_bounds (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ)
    (hK : Kᴴ*K ≤ 1) (hL : Lᴴ*L ≤ 1) :
    hsSq (K*D*Lᵀ) ≤ hsSq (K*D) ∧ hsSq (K*D*Lᵀ) ≤ hsSq (D*Lᵀ) ∧
      hsSq (K*D) ≤ hsSq D ∧ hsSq (D*Lᵀ) ≤ hsSq D := by
  have hF := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)
  have hJ := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hL)
  have hG := Matrix.posSemidef_conjTranspose_mul_self K
  have hH := Matrix.posSemidef_conjTranspose_mul_self L
  have h1 := prob_nonneg (C := D) hG hJ
  have h2 := prob_nonneg (C := D) hF hH
  have h3 := prob_nonneg (C := D) hF Matrix.PosSemidef.one
  have h4 := prob_nonneg (C := D) Matrix.PosSemidef.one hJ
  rw [prob_sub_right, prob_left_gram, prob_gram] at h1
  rw [prob_sub_left, prob_right_gram, prob_gram] at h2
  rw [prob_sub_left, prob_one, prob_left_gram] at h3
  rw [prob_sub_right, prob_one, prob_right_gram] at h4
  exact ⟨sub_nonneg.mp h1, sub_nonneg.mp h2, sub_nonneg.mp h3, sub_nonneg.mp h4⟩

end FilterMass

open Filter Topology
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


theorem solution.{u_n,u_m,u_p,u_q} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.filter_mass_bounds.{u_n,u_m,u_p,u_q} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.filter_mass_bounds.{u_n,u_m,u_p,u_q}
