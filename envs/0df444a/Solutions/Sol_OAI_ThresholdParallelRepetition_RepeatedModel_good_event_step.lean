-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.RepeatedModel.good_event_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:49:16.286665+00:00
-- url     : https://prove2.me/submissions/38d8e510-1a0c-4b85-9fe7-6862ac77474b

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ConditionedStep.lean:L50-L69
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.RepeatedModel.good_event_step. The node keeps its source
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
import Definitions.Def_OAI_Probability_EntangledGames_FreshStates
import Definitions.Def_OAI_Probability_EntangledGames_ExposureData
import Definitions.Def_OAI_Probability_EntangledGames_Refinement
import Definitions.Def_OAI_Probability_EntangledGames_ExposureErrors
import Definitions.Def_OAI_Probability_EntangledGames_Rounding
import Definitions.Def_OAI_Probability_EntangledGames_RepeatedModel
import Definitions.Def_OAI_Probability_EntangledGames_TestMoments
import Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_transportedEffect_pullback
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_EventSystem_normalized_error_bounds
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_chain_error_bounds
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_chain_fixed_mass
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_correlated_sampling_value
import Theorems.Thm_OAI_ThresholdParallelRepetition_successProbability_le_one

-- ---- from OAI.Probability.EntangledGames.Basic ----
namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder

namespace ThresholdParallelRepetition

open scoped Kronecker
open Matrix

namespace Strategy
variable {X Y A B : Type} [Fintype A] [Fintype B]

lemma born_eq_quadratic (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    S.born x y a b =
      (star S.state ⬝ᵥ ((S.alice x a ⊗ₖ S.bob y b) *ᵥ S.state)).re := by
  simp only [born, dotProduct, Matrix.mulVec, Matrix.kroneckerMap_apply, Pi.star_apply,
    Finset.mul_sum, ← mul_assoc, Complex.re_sum]

lemma born_nonneg (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.born x y a b := by
  rw [born_eq_quadratic]
  exact (Complex.nonneg_iff.mp
    (((S.alice_pos x a).kronecker (S.bob_pos y b)).dotProduct_mulVec_nonneg S.state)).1

end Strategy

namespace Strategy

end Strategy

lemma successProbability_nonneg {x y a b : ℕ} (G : Game x y a b)
    (S : SingleStrategy x y a b) : 0 ≤ successProbability G S := by
  apply Finset.sum_nonneg
  intro z _
  apply mul_nonneg (G.questionProb_nonneg z)
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact S.born_nonneg _ _ _ _
  · exact le_rfl

lemma entangledValue_nonneg {x y a b : ℕ} (G : Game x y a b) :
    0 ≤ entangledValue G := by
  let S : SingleStrategy x y a b := Strategy.deterministic 0 0
  exact (successProbability_nonneg G S).trans (le_csSup
    (show BddAbove (Set.range (successProbability G)) from
      ⟨1, by rintro _ ⟨T, rfl⟩; exact successProbability_le_one G T⟩)
    (Set.mem_range_self S))

end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Rounding ----
namespace OAI

universe u_R u_m u_n u_A u_B u_T u_U

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

namespace QuantumSampling
end QuantumSampling
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {R : Type u_R} [Fintype R] [Nonempty R]
lemma uniform_avg (f : R → ℝ) : (uniform (R := R)).avg f = (1/(Fintype.card R : ℝ))*∑ r, f r := by
  simp only [uniform, avg, smul_eq_mul, Finset.mul_sum]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
namespace ThresholdParallelRepetition
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))

include hμ
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law OperatorEntropy
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} {T : Type u_T} {U : Type u_U} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [Fintype B] [Fintype R] [Fintype T] [Fintype U]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.RepeatedModel ----
namespace OAI

universe u_X u_Y u_A u_B u_I u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable (M : RepeatedModel X Y A B I m n)
lemma indicator_nonneg (c : Finset I) (t) : 0 ≤ M.indicator c t := by
  unfold indicator; split_ifs <;> norm_num
lemma indicator_insert (c : Finset I) (i : I) (t) :
    M.indicator (insert i c) t = M.indicator c t * (if M.winsAt t i then 1 else 0) := by
  simp only [indicator, Finset.forall_mem_insert]
  split_ifs <;> simp_all
lemma mass_insert_le (c : Finset I) (i : I) : M.mass (insert i c) ≤ M.mass c := by
  apply M.joint.avg_mono
  intro t
  rw [indicator_insert]
  split_ifs <;> simp [M.indicator_nonneg]

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace FiniteProbability.Law
variable {I : Type u_I} {X : Type u_X} {Y : Type u_Y} [DecidableEq I]
end FiniteProbability.Law
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {X : Type u_X} {Y : Type u_Y} {A : Type u_A} {B : Type u_B} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable (M : RepeatedModel X Y A B I m n)

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
lemma fine_event (c : Finset I) (i : I) (z : Profile I X Y) :
    (∑ r : Records (A := A) (B := B) c, M.mask c r z *
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 a b then
        prob M.C ((M.fineA c i z).effect (r.1,a)) ((M.fineB c i z).effect (r.2,b)) else 0) =
      (M.answers z).avg (fun w => M.indicator (insert i c) (z,w)) := by
  have hh := coarsen_prob_sum M.C (M.P (fun j => (z j).1)) (M.Q (fun j => (z j).2))
    (fun a => (restrictA c a,a i)) (fun b => (restrictB c b,b i))
    (fun ra rb => M.mask c (ra.1,rb.1) z * (if M.V (z i).1 (z i).2 ra.2 rb.2 then (1:ℝ) else 0))
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul] at hh
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]
  conv_lhs => arg 2; ext ra; rw [Finset.sum_comm]
  rw [show (∑ ra, ∑ a, ∑ rb, ∑ b, if M.V (z i).1 (z i).2 a b then
      M.mask c (ra,rb) z * prob M.C ((M.fineA c i z).effect (ra,a)) ((M.fineB c i z).effect (rb,b)) else 0) =
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 (a i) (b i) then
        M.mask c (restrictA c a,restrictB c b) z * prob M.C ((M.P (fun j => (z j).1)).effect a) ((M.Q (fun j => (z j).2)).effect b) else 0 from hh]
  simp only [answers, outcomeLaw_avg, M.indicator_insert, M.mask_restrict, winsAt]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split_ifs with h <;> simp [h, mul_comm]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] in
lemma score_eq_mass_ratio (c : Finset I) (hp : 0 < M.mass c) (i : I) :
    (M.refinement c hp).score i M.V = M.mass (insert i c)/M.mass c := by
  unfold Refinement.score
  change (1/M.mass c)*∑ r : Records (A := A) (B := B) c,
    (pi (fun _ : I => M.μ)).avg (fun z => M.mask c r z *
      ∑ a, ∑ b, if M.V (z i).1 (z i).2 a b then
        prob M.C ((M.fineA c i z).effect (r.1,a)) ((M.fineB c i z).effect (r.2,b)) else 0) = _
  rw [← avg_sum]
  simp only [M.fine_event]
  rw [← M.joint_avg]
  change (1/M.mass c)*M.mass (insert i c) = _
  ring

omit [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B] [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B] in
omit [Fintype I] in
lemma card_records (c : Finset I) : Fintype.card (Records (A := A) (B := B) c) = (Fintype.card A*Fintype.card B)^c.card := by
  simp only [Records, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, mul_pow]

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI

-- ---- inlined from the conditional_rounding_small solution (its helpers and the lemma itself) ----
-- (proved here instead of imported: the platform cannot check conditional_rounding_small's published statement)
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

lemma hsSq_eq_trace (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, hsSq]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [Complex.mul_re, Complex.normSq_apply]

lemma hsSq_zero : hsSq (0 : Matrix m n ℂ) = 0 := by simp [hsSq]

lemma hsSq_blocks {q : Type u_q} [Fintype q] (A : Matrix m n ℂ) (B : Matrix m p ℂ)
    (C : Matrix q n ℂ) (D : Matrix q p ℂ) :
    hsSq (Matrix.fromBlocks A B C D) = hsSq A + hsSq B + hsSq C + hsSq D := by
  simp only [hsSq, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

omit [Fintype m] [Fintype n] [Fintype p] in
lemma fromBlocks_sub {q : Type u_q} (A A' : Matrix m n ℂ) (B B' : Matrix m p ℂ)
    (C C' : Matrix q n ℂ) (D D' : Matrix q p ℂ) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A-A') (B-B') (C-C') (D-D') := by
  ext i j
  cases i <;> cases j <;> rfl

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

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma weighted_sqrt_le {ι : Type u_ι} [Fintype ι] (w e : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hE : ∀ i, 0 ≤ e i) (hs : ∑ i, w i = 1) :
    (∑ i, w i * Real.sqrt (e i)) ≤ Real.sqrt (∑ i, w i * e i) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => w i * Real.sqrt (e i)) (f := fun i => w i) (g := fun i => w i * e i)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (hE i))
    (fun i _ => by rw [mul_pow, Real.sq_sqrt (hE i)]; exact le_of_eq (by ring))
  rw [hs, one_mul, ← Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hE i)))] at hc
  exact le_of_sq_le_sq hc (Real.sqrt_nonneg _)

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

lemma hsSq_mul_contraction {W : Matrix m n ℂ} (hW : Wᴴ*W ≤ 1)
    {p : Type u_p} [Fintype p] (M : Matrix n p ℂ) : hsSq (W*M) ≤ hsSq M := by
  have hpos := (Matrix.le_iff.mp hW).conjTranspose_mul_mul_same M
  have ht := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at ht
  rw [hsSq_eq_trace, hsSq_eq_trace]
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using sub_nonneg.mp ht

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
lemma hsSq_sub_comm (M N : Matrix m n ℂ) : hsSq (M-N) = hsSq (N-M) := by
  rw [← hsSq_neg]; congr 1; abel
lemma hsSq_smul (r : ℝ) (M : Matrix m n ℂ) : hsSq (r • M) = r^2*hsSq M := by
  simp only [hsSq, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, ← Finset.mul_sum]
  congr 1
  ring
lemma hsSq_add_le (M N : Matrix m n ℂ) : hsSq (M+N) ≤ 2*(hsSq M+hsSq N) := by
  unfold hsSq
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  simp only [Matrix.add_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((M i j).re-(N i j).re), sq_nonneg ((M i j).im-(N i j).im)]

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

end FilterMass

open Filter Topology
lemma prob_smul {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
    (r : ℝ) (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    prob (r • C) A B = r^2 * prob C A B := by
  simp only [prob, eval_eq_trace, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma payoff_smul {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B] (r : ℝ) (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) : payoff (r • C) P Q V = r^2 * payoff C P Q V := by
  simp only [payoff, prob_smul, Finset.mul_sum, mul_ite, mul_zero]

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
end Norm

section WinEffect
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype A] [Fintype B]
lemma winEffect_pos (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    (winEffect P Q V).PosSemidef := by
  apply Matrix.posSemidef_sum; intro a _
  apply Matrix.posSemidef_sum; intro b _
  split
  · exact (P.pos a).kronecker (Q.pos b)
  · exact Matrix.PosSemidef.zero
lemma winEffect_le_one (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    winEffect P Q V ≤ 1 := by
  have hsum : (∑ a, ∑ b, P.effect a ⊗ₖ Q.effect b) = (1 : Matrix (m × n) (m × n) ℂ) := by
    simp only [← kronecker_sum_right, ← kronecker_sum_left, P.total, Q.total,
      Matrix.one_kronecker_one]
  rw [← hsum]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact le_rfl
  · exact ((P.pos a).kronecker (Q.pos b)).nonneg

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_flat (C : Matrix m n ℂ) : hsSq (flat C) = hsSq C := by
  simp [hsSq, flat, vec, Fintype.sum_prod_type]
omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma flat_sub (C D : Matrix m n ℂ) : flat (C-D) = flat C-flat D := rfl
omit [DecidableEq m] [DecidableEq n] in
lemma flat_form (C : Matrix m n ℂ) (W : Matrix (m × n) (m × n) ℂ) :
    Matrix.trace ((flat C)ᴴ*(W*flat C)) = star (vec C) ⬝ᵥ (W *ᵥ vec C) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique, Matrix.mul_apply,
    Matrix.conjTranspose_apply, flat, Matrix.replicateCol_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]
lemma payoff_eq_form (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) :
    payoff C P Q V = (star (vec C) ⬝ᵥ (winEffect P Q V *ᵥ vec C)).re := by
  simp only [winEffect, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, payoff]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  split
  · rfl
  · simp only [Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
lemma payoff_eq_hsSq (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) :
    payoff C P Q V = hsSq (CFC.sqrt (winEffect P Q V) * flat C) := by
  rw [hsSq_eq_trace, Matrix.conjTranspose_mul]
  have hh : (CFC.sqrt (winEffect P Q V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  rw [hh.eq, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt _) (CFC.sqrt _),
    CFC.sqrt_mul_sqrt_self _ (winEffect_pos P Q V).nonneg, flat_form, payoff_eq_form]
lemma winSqrt_contraction (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    (CFC.sqrt (winEffect P Q V))ᴴ*CFC.sqrt (winEffect P Q V) ≤ 1 := by
  have hh : (CFC.sqrt (winEffect P Q V)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  rw [hh.eq, CFC.sqrt_mul_sqrt_self _ (winEffect_pos P Q V).nonneg]
  exact winEffect_le_one P Q V
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

-- ---- from OAI.Probability.EntangledGames.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

lemma avg_add (p : Law α) (f g : α → E) :
    p.avg (fun x => f x+g x) = p.avg f+p.avg g := by
  simp [avg, smul_add, Finset.sum_add_distrib]
lemma avg_sub {F : Type u_F} [AddCommGroup F] [Module ℝ F]
    (p : Law α) (f g : α → F) :
    p.avg (fun x => f x-g x) = p.avg f-p.avg g := by
  simp only [avg, smul_sub, Finset.sum_sub_distrib]
lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
section Pair
variable [DecidableEq α] [DecidableEq β]

end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_X u_Y u_I u_E u_F u_R

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability
namespace Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [DecidableEq X] [DecidableEq Y] [AddCommMonoid E] [Module ℝ E]

omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_right_comm (z : Profile I X Y) (i j : I) (x : X) (y : Y) :
    updateLeft (updateRight z j y) i x = updateRight (updateLeft z i x) j y := by
  by_cases hij : i = j
  · subst j; simp [updateLeft, updateRight]
  · simp only [updateLeft, updateRight, Function.update_of_ne hij,
      Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm (Ne.symm hij) _ _ z

omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresLeft (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E) :
    IgnoresLeft (μ.left x₀ i f) i := by
  intro z x
  simp only [left, updateLeft, Function.update_self]
  congr 1
  funext x'
  simp [Function.update_idem]
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresRight (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    IgnoresRight (μ.right y₀ i f) i := by
  intro z y
  simp only [right, updateRight, Function.update_self]
  congr 1
  funext y'
  simp [Function.update_idem]

omit [Fintype I] [DecidableEq Y] in
lemma left_ignoresRight_other (μ : Law (X×Y)) (x₀ : X) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresRight f j) : IgnoresRight (μ.left x₀ i f) j := by
  intro z y
  have hi : updateRight z j y i = z i := Function.update_of_ne hij _ _
  simp only [left, hi]
  congr 1
  funext u
  rw [updateLeft_right_comm, hf _ _]
omit [Fintype I] [DecidableEq X] in
lemma right_ignoresLeft_other (μ : Law (X×Y)) (y₀ : Y) {i j : I} (hij : i ≠ j)
    {f : Profile I X Y → E} (hf : IgnoresLeft f j) : IgnoresLeft (μ.right y₀ i f) j := by
  intro z x
  have hi : updateLeft z j x i = z i := Function.update_of_ne hij _ _
  simp only [right, hi]
  congr 1
  funext u
  rw [← updateLeft_right_comm, hf _ _]

section Linear
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Linear

section Folds

omit [Fintype I] [DecidableEq Y] in
lemma lefts_ignoresRight_notMem (μ : Law (X×Y)) (x₀ : X) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresRight f i) :
    IgnoresRight (μ.lefts x₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact left_ignoresRight_other μ x₀ (Ne.symm h.1) (ih h.2)

omit [Fintype I] [DecidableEq X] in
lemma rights_ignoresLeft_notMem (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    {f : Profile I X Y → E} {i : I} (hi : i ∉ l) (hf : IgnoresLeft f i) :
    IgnoresLeft (μ.rights y₀ l f) i := by
  induction l with
  | nil => exact hf
  | cons j l ih =>
    have h : i ≠ j ∧ i ∉ l := by simpa only [List.mem_cons, not_or] using hi
    exact right_ignoresLeft_other μ y₀ (Ne.symm h.1) (ih h.2)

variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end Folds

section FixedCoordinate
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
end FixedCoordinate

section FoldLinear
variable {R : Type u_R} {F : Type u_F} [Fintype R] [AddCommMonoid F] [Module ℝ F]
end FoldLinear

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI

-- ---- from OAI.Probability.EntangledGames.ExposureChain ----
namespace OAI

universe u_I u_X u_Y u_R u_m u_n u_E u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

lemma list_suffix_prefix_disjoint {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ) :
    ∀ i ∈ l.drop j, i ∉ (l.take j).reverse := by
  have h : (l.take j ++ l.drop j).Nodup := by simpa using hN
  have hd := (List.nodup_append.mp h).2.2
  intro i hi hi'
  exact hd i (List.mem_reverse.mp hi') i hi rfl

lemma list_fresh_not_suffix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ l.drop (j+1) := by
  have h : (l.drop j).Nodup := hN.drop
  rw [List.drop_eq_getElem_cons hj] at h
  exact (List.nodup_cons.mp h).1

lemma list_fresh_not_prefix {I : Type u_I} (l : List I) (hN : l.Nodup) (j : ℕ)
    (hj : j < l.length) : l[j] ∉ (l.take j).reverse := by
  apply list_suffix_prefix_disjoint l hN j l[j]
  rw [List.drop_eq_getElem_cons hj]
  exact List.mem_cons_self

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {E : Type u_E} [AddCommMonoid E] [Module ℝ E]
omit [Fintype I] [DecidableEq Y] [Fintype R] in
lemma chainLeft_step (μ : Law (X×Y)) (x₀ : X) (l : List I) (F : R → Profile I X Y → E)
    (j : ℕ) (hj : j < l.length) (r : R) :
    chainLeft μ x₀ l F j r = μ.left x₀ l[j] (chainLeft μ x₀ l F (j+1) r) := by
  unfold chainLeft
  rw [List.drop_eq_getElem_cons hj]
  rfl
omit [Fintype I] [DecidableEq X] [Fintype R] in
lemma chainRight_step (μ : Law (X×Y)) (y₀ : Y) (l : List I) (H : R → Profile I X Y → E)
    (j : ℕ) (hj : j < l.length) (r : R) :
    chainRight μ y₀ l H (j+1) r = μ.right y₀ l[j] (chainRight μ y₀ l H j r) := by
  unfold chainRight
  rw [List.take_succ_eq_append_getElem hj, List.reverse_append]
  rfl

omit [Fintype I] [DecidableEq Y] [Fintype R] in
lemma chainLeft_next_local (μ : Law (X×Y)) (x₀ : X) (l : List I) (hN : l.Nodup)
    (F : R → Profile I X Y → E) (hF : ∀ r i, IgnoresRight (F r) i)
    (j : ℕ) (hj : j < l.length) (r : R) :
    IgnoresRight (chainLeft μ x₀ l F (j+1) r) l[j] :=
  lefts_ignoresRight_notMem μ x₀ _ (list_fresh_not_suffix l hN j hj) (hF r _)
omit [Fintype I] [DecidableEq X] [Fintype R] in
lemma chainRight_prev_local (μ : Law (X×Y)) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (H : R → Profile I X Y → E) (hH : ∀ r i, IgnoresLeft (H r) i)
    (j : ℕ) (hj : j < l.length) (r : R) :
    IgnoresLeft (chainRight μ y₀ l H j r) l[j] :=
  rights_ignoresLeft_notMem μ y₀ _ (list_fresh_not_prefix l hN j hj) (hH r _)

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq X] [DecidableEq Y]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

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
lemma trace_blockDiagonal (C : R → Matrix m m ℂ) :
    Matrix.trace (Matrix.blockDiagonal C) = ∑ r, Matrix.trace (C r) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.blockDiagonal_apply_eq]
  exact Finset.sum_comm

lemma hsSq_blockDiagonal (C : R → Matrix m n ℂ) :
    hsSq (Matrix.blockDiagonal C) = ∑ r, hsSq (C r) := by
  simp only [hsSq_eq_trace, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    trace_blockDiagonal, Complex.re_sum]

lemma prob_blockDiagonal (C : R → Matrix m n ℂ) (A : R → Matrix m m ℂ)
    (B : R → Matrix n n ℂ) :
    prob (Matrix.blockDiagonal C) (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      ∑ r, prob (C r) (A r) (B r) := by
  simp only [prob, eval_eq_trace, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul,
    Matrix.blockDiagonal_transpose, trace_blockDiagonal, Complex.re_sum]

variable [DecidableEq m]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq n]
lemma payoff_blockDiagonal (C : R → Matrix m n ℂ) (P : R → POVM m A) (Q : R → POVM n B)
    (V : A → B → Bool) :
    payoff (Matrix.blockDiagonal C) (POVM.blocks P) (POVM.blocks Q) V =
      ∑ r, payoff (C r) (P r) (Q r) V := by
  simp only [payoff, POVM.blocks, prob_blockDiagonal]
  calc
    _ = ∑ a, ∑ b, ∑ r, if V a b then prob (C r) ((P r).effect a) ((Q r).effect b) else 0 := by
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      split <;> simp_all
    _ = _ := by
      conv_rhs =>
        rw [Finset.sum_comm]
        arg 2
        ext a
        rw [Finset.sum_comm]
end Blocks

section Normalization
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
lemma hsSq_unitize (C D : Matrix m n ℂ) (hD : hsSq D = 1) : hsSq (unitize C D) = 1 := by
  unfold unitize
  split_ifs with h
  · exact hD
  · rw [hsSq_smul, inv_pow, Real.sq_sqrt (hsSq_nonneg C)]
    exact inv_mul_cancel₀ h

lemma hsSq_difference_unbounded (C D : Matrix m n ℂ) (hD : hsSq D ≤ 1) :
    hsSq C - hsSq D ≤ 2*Real.sqrt (hsSq (C-D)) + hsSq (C-D) := by
  have ht : ‖C‖ ≤ ‖D‖ + ‖C-D‖ := by
    simpa only [norm_sub_rev] using norm_le_insert D C
  have hd := hsSq_le_one_norm hD
  have hc0 := norm_nonneg C
  have hd0 := norm_nonneg D
  have he0 := norm_nonneg (C-D)
  have ht2 := sq_le_sq₀ hc0 (add_nonneg hd0 he0) |>.2 ht
  simp only [norm_eq_sqrt_hsSq] at ht2 hd hd0 he0
  have hmul := mul_le_mul_of_nonneg_right hd he0
  rw [Real.sq_sqrt (hsSq_nonneg C)] at ht2
  nlinarith [Real.sq_sqrt (hsSq_nonneg D), Real.sq_sqrt (hsSq_nonneg (C-D))]
end Normalization

section Payoff
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Fintype A] [Fintype B]
lemma payoff_difference_unbounded (C D : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) (hD : hsSq D ≤ 1) :
    payoff C P Q V - payoff D P Q V ≤ 2*Real.sqrt (hsSq (C-D)) + hsSq (C-D) := by
  have hsd := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat D)).trans
    (le_trans (le_of_eq (hsSq_flat D)) hD)
  rw [payoff_eq_hsSq, payoff_eq_hsSq]
  refine (hsSq_difference_unbounded _ _ hsd).trans ?_
  have he : hsSq (CFC.sqrt (winEffect P Q V)*flat C-CFC.sqrt (winEffect P Q V)*flat D) ≤ hsSq (C-D) := by
    rw [← Matrix.mul_sub, ← flat_sub]
    exact (hsSq_mul_contraction (winSqrt_contraction P Q V) _).trans_eq (hsSq_flat _)
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (by norm_num)) he
end Payoff
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_squareState (C : Matrix m n ℂ) : hsSq (squareState C) = hsSq C := by
  simp only [squareState, hsSq_blocks, hsSq_zero, zero_add, add_zero]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
lemma squareState_sub (C D : Matrix m n ℂ) : squareState (C-D) = squareState C-squareState D := by
  simp only [squareState, fromBlocks_sub, sub_self]

variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B]
omit [DecidableEq m] [DecidableEq n] in
lemma prob_squareState (C : Matrix m n ℂ) (A₁ : Matrix m m ℂ) (A₂ : Matrix n n ℂ)
    (B₁ : Matrix m m ℂ) (B₂ : Matrix n n ℂ) :
    prob (squareState C) (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂) =
      prob C A₁ B₂ := by
  simp only [prob, eval_eq_trace, squareState, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_transpose, Matrix.conjTranspose_zero, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Finset.sum_const_zero, zero_add]

lemma payoff_squareState (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (a₀ : A) (b₀ : B) (V : A → B → Bool) :
    payoff (squareState C) (P.sum (POVM.default a₀)) ((POVM.default b₀).sum Q) V = payoff C P Q V := by
  simp only [payoff, POVM.sum, prob_squareState]
end ThresholdParallelRepetition.QuantumSampling

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law
section Stack
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
lemma hsSq_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ) :
    hsSq (weightedBlock w C) = ∑ r, w r*hsSq (C r) := by
  simp only [weightedBlock, hsSq_blockDiagonal, hsSq_smul, Real.sq_sqrt (hw _)]
omit [Fintype m] [Fintype n] [Fintype R] in
lemma weightedBlock_sub (w : R → ℝ) (C D : R → Matrix m n ℂ) :
    weightedBlock w (fun r => C r-D r) = weightedBlock w C-weightedBlock w D := by
  simp only [weightedBlock, smul_sub]
  exact Matrix.blockDiagonal_sub _ _
lemma hsSq_weightedBlock_sub (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C D : R → Matrix m n ℂ) :
    hsSq (weightedBlock w C-weightedBlock w D) = ∑ r, w r*hsSq (C r-D r) := by
  rw [← weightedBlock_sub, hsSq_weightedBlock w hw]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
lemma payoff_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ)
    (P : R → POVM m A) (Q : R → POVM n B) (V : A → B → Bool) :
    payoff (weightedBlock w C) (POVM.blocks P) (POVM.blocks Q) V =
      ∑ r, w r*payoff (C r) (P r) (Q r) V := by
  simp only [weightedBlock, payoff_blockDiagonal, payoff_smul, Real.sq_sqrt (hw _)]
end Stack

lemma correlated_sampling_value_rect {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix m n ℂ) (N : Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by
  have hh := correlated_sampling_value G (fun x => squareState (M x)) (fun y => squareState (N y))
    (fun x => (hsSq_squareState _).trans (hM x)) (fun y => (hsSq_squareState _).trans (hN y))
    (fun x => (P x).sum (POVM.default 0)) (fun y => (POVM.default 0).sum (Q y)) hε hε1
  simpa only [payoff_squareState, ← squareState_sub, hsSq_squareState] using hh

lemma avg_payoff_difference_unbounded {Z : Type u_Z} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype Z] [Fintype m] [Fintype n]
    [Fintype A] [Fintype B] [DecidableEq m] [DecidableEq n]
    (μ : Law Z) (C D : Z → Matrix m n ℂ) (hD : ∀ z, hsSq (D z) ≤ 1)
    (P : Z → POVM m A) (Q : Z → POVM n B) (V : Z → A → B → Bool) :
    μ.avg (fun z => payoff (C z) (P z) (Q z) (V z)) -
      μ.avg (fun z => payoff (D z) (P z) (Q z) (V z)) ≤
      2*Real.sqrt (μ.avg (fun z => hsSq (C z-D z))) + μ.avg (fun z => hsSq (C z-D z)) := by
  rw [← avg_sub]
  have he := μ.avg_mono (fun z => payoff_difference_unbounded (C z) (D z) (P z) (Q z) (V z) (hD z))
  apply he.trans
  rw [avg_add]
  apply add_le_add _ (le_refl _)
  rw [show (fun z => 2*Real.sqrt (hsSq (C z-D z))) = (fun z => (2:ℝ) • Real.sqrt (hsSq (C z-D z))) from rfl,
    avg_smul]
  exact mul_le_mul_of_nonneg_left (weighted_sqrt_le _ _ μ.nonneg (fun z => hsSq_nonneg _) μ.total) (by norm_num)
end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.FreshStates ----
namespace OAI

universe u_X u_Y u_I u_E u_R u_m u_n u_u u_v u_Z

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [DecidableEq I]
lemma ignoresRight_update {f : Profile I X Y → E} {i : I} (hf : IgnoresRight f i)
    (z : Profile I X Y) (x : X) (y y' : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x,y')) := by
  simpa [updateRight] using hf (Function.update z i (x,y')) y
lemma ignoresLeft_update {f : Profile I X Y → E} {i : I} (hf : IgnoresLeft f i)
    (z : Profile I X Y) (x x' : X) (y : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x',y)) := by
  simpa [updateLeft] using hf (Function.update z i (x',y)) x
lemma ignores_update {f : Profile I X Y → E} {i : I} (hL : IgnoresLeft f i) (hR : IgnoresRight f i)
    (z : Profile I X Y) (q : X×Y) : f (Function.update z i q) = f z := by
  obtain ⟨x,y⟩ := q
  rw [ignoresRight_update hR z x y (z i).2]
  exact hL z x
end ThresholdParallelRepetition.FiniteProbability.Law
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [DecidableEq X] [DecidableEq Y]
omit [DecidableEq R] [DecidableEq X] [DecidableEq Y] in
lemma fresh_avg_weighted (μ : Law (X×Y)) (i : I) (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r, IgnoresLeft (θ r) i) (hθR : ∀ r, IgnoresRight (θ r) i)
    (g : R → Profile I X Y → ℝ) :
    μ.avg (fun q => ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*g r (Function.update z i q))) =
      ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*g r z) := by
  rw [avg_sum]
  apply Finset.sum_congr rfl; intro r _
  have he : (fun q => (pi (fun _ : I => μ)).avg (fun z => θ r z*g r (Function.update z i q))) =
      (fun q => (pi (fun _ : I => μ)).avg (fun z => θ r (Function.update z i q)*g r (Function.update z i q))) := by
    funext q
    congr 1
    funext z
    rw [ignores_update (hθL r) (hθR r)]
  rw [he, avg_comm]
  exact pi_avg_update _ i (fun z => θ r z*g r z)

variable {m : Type u_m} {n : Type u_n} {u : Type u_u} {v : Type u_v} [Fintype m] [Fintype n] [Fintype u] [Fintype v]
lemma stateAt_distance_left (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U U' : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q-stateAt μ θ p i C U' V q) =
      (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
        ((U r (Function.update z i q)-U' r (Function.update z i q))*C*(V r (Function.update z i q))ᵀ)) := by
  simp only [stateAt]
  rw [hsSq_weightedBlock_sub _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum, Matrix.sub_mul]
  apply Finset.sum_congr rfl; intro z _
  ring

lemma stateAt_distance_right (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V V' : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q-stateAt μ θ p i C U V' q) =
      (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
        (U r (Function.update z i q)*C*(V r (Function.update z i q)-V' r (Function.update z i q))ᵀ)) := by
  simp only [stateAt]
  rw [hsSq_weightedBlock_sub _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum, Matrix.transpose_sub, Matrix.mul_sub]
  apply Finset.sum_congr rfl; intro z _
  ring
omit [Fintype R] [Fintype u] [Fintype v] in
lemma stateAt_right_local (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (hU : ∀ r, IgnoresRight (U r) i) (hV : ∀ r, IgnoresRight (V r) i)
    (x : X) (y y' : Y) : stateAt μ θ p i C U V (x,y) = stateAt μ θ p i C U V (x,y') := by
  unfold stateAt
  congr 1
  funext t
  rw [ignoresRight_update (hU t.1) t.2 x y y', ignoresRight_update (hV t.1) t.2 x y y']

omit [Fintype R] [Fintype u] [Fintype v] in
lemma stateAt_left_local (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (hU : ∀ r, IgnoresLeft (U r) i) (hV : ∀ r, IgnoresLeft (V r) i)
    (x x' : X) (y : Y) : stateAt μ θ p i C U V (x,y) = stateAt μ θ p i C U V (x',y) := by
  unfold stateAt
  congr 1
  funext t
  rw [ignoresLeft_update (hU t.1) t.2 x x' y, ignoresLeft_update (hV t.1) t.2 x x' y]

variable [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
-- [generator] trimmed: open FiniteProbability Law ScalarEntropy
open FiniteProbability Law
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
lemma hsSq_basisState (i : m) (j : n) : hsSq (basisState i j) = 1 := by
  have he : basisState i j = fun a b => if a=i then (if b=j then 1 else 0) else 0 := by
    ext a b
    by_cases h : a=i <;> simp [basisState, h]
  rw [he]
  simp [hsSq, apply_ite]

omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_triangle (C D E : Matrix m n ℂ) : hsSq (C-E) ≤ 2*(hsSq (C-D)+hsSq (D-E)) := by
  have h := hsSq_add_le (C-D) (D-E)
  simpa only [sub_add_sub_cancel] using h

variable {X : Type u_X} {Y : Type u_Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.ExposureData ----
namespace OAI

universe u_X u_Y u_I u_R u_m u_n

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable (X : Type u_X) (Y : Type u_Y) (I : Type u_I) (R : Type u_R) (m : Type u_m) (n : Type u_n) [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [DecidableEq R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {X Y I R m n} [Nonempty X] [Nonempty Y] [Nonempty R]
namespace EventSystem
variable (S : EventSystem X Y I R m n)
lemma rawA_eq (j : Fin S.l.length) (q : X×Y) : S.rawA j q.1 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U (j+1)) (S.V (j+1)) q := by
  apply stateAt_right_local
  · intro r z y
    exact congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  · intro r z y
    apply congrArg (commonMap S.B)
    rw [h, chainRight_step S.μ S.y₀ S.l S.H j j.isLt r]
    exact right_ignoresRight S.μ S.y₀ _ _ z y
lemma rawB_eq (j : Fin S.l.length) (q : X×Y) : S.rawB j q.2 =
    stateAt S.μ S.θ S.p S.l[j.val] S.C (S.U j) (S.V j) q := by
  apply stateAt_left_local
  · intro r z x
    apply congrArg (commonMap S.A)
    rw [f, chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r]
    exact left_ignoresLeft S.μ S.x₀ _ _ z x
  · intro r z x
    exact congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)

end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Refinement ----
namespace OAI

universe u_m u_n u_A u_X u_Y u_I u_R u_B

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling.POVM
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype A] [DecidableEq A]
lemma transport_pullback (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (hGT : ∑ a, G a = Fᴴ*F) (a₀ a : A) :
    Fᴴ*(transport F G hG hGT a₀).effect a*F = G a :=
  transportedEffect_pullback F G hG hGT a₀ a
end QuantumSampling.POVM
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)
omit [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma leftFine_local (j : Fin S.l.length) (r : R) (a : A) : IgnoresRight (fun z => T.leftFine j r z a) S.l[j.val] :=
  lefts_ignoresRight_notMem S.μ S.x₀ _ (list_fresh_not_suffix S.l S.nodup j j.isLt) (T.left_local _ r a _)
omit [DecidableEq X] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] [DecidableEq A] [DecidableEq B] in
lemma rightFine_local (j : Fin S.l.length) (r : R) (b : B) : IgnoresLeft (fun z => T.rightFine j r z b) S.l[j.val] :=
  rights_ignoresLeft_notMem S.μ S.y₀ _ (list_fresh_not_prefix S.l S.nodup j j.isLt) (T.right_local _ r b _)

omit [DecidableEq B] in
lemma leftPOVM_local (a₀ : A) (j : Fin S.l.length) (r : R) : IgnoresRight (T.leftPOVM a₀ j r) S.l[j.val] := by
  intro z y
  have hU : S.U (j+1) r (updateRight z S.l[j.val] y) = S.U (j+1) r z :=
    congrArg (commonMap S.A) (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt r z y)
  have hF : T.leftFine j r (updateRight z S.l[j.val] y) = T.leftFine j r z := by
    funext a; exact T.leftFine_local j r a z y
  simp only [leftPOVM, hU, hF]
omit [DecidableEq A] in
lemma rightPOVM_local (b₀ : B) (j : Fin S.l.length) (r : R) : IgnoresLeft (T.rightPOVM b₀ j r) S.l[j.val] := by
  intro z x
  have hV : S.V j r (updateLeft z S.l[j.val] x) = S.V j r z :=
    congrArg (commonMap S.B) (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt r z x)
  have hH : T.rightFine j r (updateLeft z S.l[j.val] x) = T.rightFine j r z := by
    funext b; exact T.rightFine_local j r b z x
  simp only [rightPOVM, hV, hH]

omit [DecidableEq B] in
lemma P_effect (a₀ : A) (j : Fin S.l.length) (q : X×Y) (a : A) :
    (T.P a₀ j q.1).effect a =
      Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] q)).effect a) := by
  change Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.leftPOVM a₀ j t.1 (Function.update t.2 S.l[j.val] (q.1,S.y₀))).effect a) = _
  apply congrArg Matrix.blockDiagonal
  funext t
  rw [ignoresRight_update (T.leftPOVM_local a₀ j t.1) t.2 q.1 S.y₀ q.2]
omit [DecidableEq A] in
lemma Q_effect (b₀ : B) (j : Fin S.l.length) (q : X×Y) (b : B) :
    (T.Q b₀ j q.2).effect b =
      Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] q)).effect b) := by
  change Matrix.blockDiagonal (fun t : R×Profile I X Y => (T.rightPOVM b₀ j t.1 (Function.update t.2 S.l[j.val] (S.x₀,q.2))).effect b) = _
  apply congrArg Matrix.blockDiagonal
  funext t
  rw [ignoresLeft_update (T.rightPOVM_local b₀ j t.1) t.2 S.x₀ q.1 q.2]

lemma transported_prob (a₀ : A) (b₀ : B) (j : Fin S.l.length) (r : R) (z : Profile I X Y) (a : A) (b : B) :
    prob (S.U (j+1) r z*S.C*(S.V j r z)ᵀ) ((T.leftPOVM a₀ j r z).effect a) ((T.rightPOVM b₀ j r z).effect b) =
      prob S.C (T.leftFine j r z a) (T.rightFine j r z b) := by
  rw [← prob_pullback]
  simp only [leftPOVM, rightPOVM, POVM.transport_pullback]
end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law MeasurementTransport
namespace QuantumSampling
variable {m : Type u_m} {n : Type u_n} {R : Type u_R} [Fintype m] [Fintype n] [Fintype R] [DecidableEq R]
lemma prob_weightedBlock (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (C : R → Matrix m n ℂ)
    (P : R → Matrix m m ℂ) (Q : R → Matrix n n ℂ) :
    prob (weightedBlock w C) (Matrix.blockDiagonal P) (Matrix.blockDiagonal Q) = ∑ r, w r*prob (C r) (P r) (Q r) := by
  simp only [weightedBlock, prob_blockDiagonal, prob_smul, Real.sq_sqrt (hw _)]
end QuantumSampling
namespace MixedExposure
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
namespace Refinement
variable {S : EventSystem X Y I R m n} (T : Refinement S A B)

lemma prob_D (a₀ : A) (b₀ : B) (j : Fin S.l.length) (q : X×Y) (a : A) (b : B) :
    prob (S.D j q) ((T.P a₀ j q.1).effect a) ((T.Q b₀ j q.2).effect b) =
      massAt S.μ S.θ S.p S.l[j.val] S.C (fun r z => T.left S.l[j.val] r z a) (fun r z => T.right S.l[j.val] r z b) q := by
  rw [T.P_effect a₀ j q a, T.Q_effect b₀ j q b]
  simp only [EventSystem.D, stateAt]
  rw [prob_weightedBlock (fun t : R×Profile I X Y => (pi (fun _ : I => S.μ)).weight t.2*S.θ t.1 t.2/S.p)
    (fun t => div_nonneg (mul_nonneg ((pi (fun _ : I => S.μ)).nonneg t.2) (S.hθ t.1 t.2)) S.hp.le)]
  simp only [T.transported_prob, Fintype.sum_prod_type]
  have he : (∑ r, ∑ z, (pi (fun _ : I => S.μ)).weight z*S.θ r z/S.p *
      prob S.C (T.leftFine j r (Function.update z S.l[j.val] q) a) (T.rightFine j r (Function.update z S.l[j.val] q) b)) =
      massAt S.μ S.θ S.p S.l[j.val] S.C
        (chainLeft S.μ S.x₀ S.l (fun r z => T.left S.l[j.val] r z a) (j+1))
        (chainRight S.μ S.y₀ S.l (fun r z => T.right S.l[j.val] r z b) j) q := by
    unfold massAt
    simp only [avg, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro z _
    change _ = (1/S.p)*((pi (fun _ : I => S.μ)).weight z*(_*_))
    simp only [leftFine, rightFine, chainLeft, chainRight]
    ring
  rw [he]
  exact chain_fixed_mass S.μ S.x₀ S.y₀ S.l S.nodup S.C _ _
    (fun r i => T.left_local _ r a i) (fun r i => T.right_local _ r b i)
    S.θ S.localθL S.localθR S.p j q

omit [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y] [DecidableEq R] [Nonempty R] in
lemma avg_if_massAt (i : I) (hi : i ∈ S.l) (V : X×Y → Bool)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ) :
    S.μ.avg (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V (z i) then prob S.C (F r z) (H r z) else 0)) := by
  have he : (fun q => if V q then massAt S.μ S.θ S.p i S.C F H q else 0) =
      (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z *
        (if V ((Function.update z i q) i) then prob S.C (F r (Function.update z i q)) (H r (Function.update z i q)) else 0))) := by
    funext q
    simp only [Function.update_self]
    split <;> simp_all [massAt, avg, smul_eq_mul]
  rw [he, avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ i S.θ
    (fun r => S.localθL r i hi) (fun r => S.localθR r i hi)
    (fun r z => if V (z i) then prob S.C (F r z) (H r z) else 0)

lemma payoff_D_eq_score (a₀ : A) (b₀ : B) (j : Fin S.l.length) (V : X → Y → A → B → Bool) :
    S.μ.avg (fun q => payoff (S.D j q) (T.P a₀ j q.1) (T.Q b₀ j q.2) (V q.1 q.2)) = T.score S.l[j.val] V := by
  simp only [payoff, T.prob_D, avg_sum]
  simp only [avg_if_massAt (S := S) S.l[j.val] (List.getElem_mem j.isLt)]
  unfold score
  simp only [Finset.mul_sum, avg_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Refinement
end MixedExposure
end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.ExposureErrors ----
namespace OAI

universe u_I u_Z u_X u_Y u_R u_m u_n

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {I : Type u_I} {Z : Type u_Z} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I] [Nonempty X] [Nonempty Y]
  [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
namespace EventSystem
variable (S : EventSystem X Y I R m n)

lemma rawA_error_eq (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)) =
    (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      (S.U (j+1) r z*S.C*(S.V j r z-S.V (j+1) r z)ᵀ)) := by
  simp only [S.rawA_eq, D, stateAt_distance_right S.μ S.θ S.hθ S.hp]
  change S.μ.avg (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      (S.U (j+1) r (Function.update z S.l[j.val] q)*S.C*
        (S.V j r (Function.update z S.l[j.val] q)-S.V (j+1) r (Function.update z S.l[j.val] q))ᵀ))) = _
  rw [avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ _ S.θ
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt))
    (fun r z => hsSq (S.U (j+1) r z*S.C*(S.V j r z-S.V (j+1) r z)ᵀ))
lemma rawB_error_eq (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2)) =
    (1/S.p)*∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      ((S.U (j+1) r z-S.U j r z)*S.C*(S.V j r z)ᵀ)) := by
  simp only [S.rawB_eq, D, stateAt_distance_left S.μ S.θ S.hθ S.hp]
  change S.μ.avg (fun q => (1/S.p) • ∑ r, (pi (fun _ : I => S.μ)).avg (fun z => S.θ r z * hsSq
      ((S.U (j+1) r (Function.update z S.l[j.val] q)-S.U j r (Function.update z S.l[j.val] q))*S.C*
        (S.V j r (Function.update z S.l[j.val] q))ᵀ))) = _
  rw [avg_smul]
  congr 1
  exact fresh_avg_weighted S.μ _ S.θ
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt))
    (fun r z => hsSq ((S.U (j+1) r z-S.U j r z)*S.C*(S.V j r z)ᵀ))

lemma raw_error_bounds :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1))) ≤ Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2))) ≤ Real.log ((Fintype.card R : ℝ)/S.p) := by
  have hh := chain_error_bounds S.μ S.x₀ S.y₀ S.l S.nodup S.C S.hC.le S.F S.H
    S.hF S.hF1 S.hH S.hH1 S.localF S.localH S.θ S.hθ S.hθ1 S.localθL S.localθR S.hp S.mass
  dsimp only at hh
  simp only [S.rawA_error_eq, S.rawB_error_eq, ← Finset.mul_sum]
  constructor
  · have h := mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ 1/S.p from div_nonneg zero_le_one S.hp.le)
    simpa only [U, V, ← mul_assoc, one_div, inv_mul_cancel₀ S.hp.ne', one_mul] using h
  · have h := mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ 1/S.p from div_nonneg zero_le_one S.hp.le)
    simpa only [U, V, ← mul_assoc, one_div, inv_mul_cancel₀ S.hp.ne', one_mul] using h

lemma M_unit (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) (x : X) : hsSq (S.M j E x) = 1 := hsSq_unitize _ _ hE
lemma N_unit (j : Fin S.l.length) (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) (y : Y) : hsSq (S.N j E y) = 1 := hsSq_unitize _ _ hE

end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- from OAI.Probability.EntangledGames.Rounding ----
namespace OAI

universe u_R u_m u_n u_A u_B u_T u_U

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law

namespace QuantumSampling
lemma rounding_value_rect {m n : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (D : Fin (x+1)×Fin (y+1) → Matrix m n ℂ)
    (M : Fin (x+1) → Matrix m n ℂ) (N : Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {eA eB : ℝ}
    (hA : G.questionLaw.avg (fun z => hsSq (D z-M z.1)) ≤ eA)
    (hB : G.questionLaw.avg (fun z => hsSq (D z-N z.2)) ≤ eB)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    G.questionLaw.avg (fun z => payoff (D z) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) +
        2*Real.sqrt eA+eA := by
  have hη : G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)) ≤ 2*(eA+eB) := by
    have he := G.questionLaw.avg_mono (fun z => hsSq_triangle (M z.1) (D z) (N z.2))
    have heq : G.questionLaw.avg (fun z => 2*(hsSq (M z.1-D z)+hsSq (D z-N z.2))) =
        2*(G.questionLaw.avg (fun z => hsSq (D z-M z.1))+G.questionLaw.avg (fun z => hsSq (D z-N z.2))) := by
      simp only [hsSq_sub_comm (M _), show (fun z => 2*(hsSq (D z-M z.1)+hsSq (D z-N z.2))) =
        (fun z => (2:ℝ) • (hsSq (D z-M z.1)+hsSq (D z-N z.2))) from rfl, avg_smul, avg_add, smul_eq_mul]
    rw [heq] at he
    linarith
  have hround := correlated_sampling_value_rect G M N hM hN P Q hε hε1
  change G.questionLaw.avg (fun z => payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤
    entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)))) at hround
  have hloss := avg_payoff_difference_unbounded G.questionLaw D (fun z => M z.1)
    (fun z => (hM z.1).le) (fun z => P z.1) (fun z => Q z.2) (fun z => G.accepts z.1 z.2)
  have hsA := Real.sqrt_le_sqrt hA
  have hsη : Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2))) ≤
      Real.sqrt (4*(eA+eB)) := Real.sqrt_le_sqrt (by linarith)
  have hsamp : Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*G.questionLaw.avg (fun z => hsSq (M z.1-N z.2)))) ≤
      Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) := by
    apply Real.sqrt_le_sqrt
    linarith [mul_le_mul_of_nonneg_left hsη (show (0:ℝ) ≤ 12/ε from div_nonneg (by norm_num) hε.le)]
  linarith

lemma rounding_value_modes {m n R : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    [Fintype n] [DecidableEq n] [Nonempty n] [Fintype R] [DecidableEq R] [Nonempty R]
    {x y a b : ℕ} (G : Game x y a b) (ρ : Law R)
    (D : R → Fin (x+1)×Fin (y+1) → Matrix m n ℂ)
    (M : R → Fin (x+1) → Matrix m n ℂ) (N : R → Fin (y+1) → Matrix m n ℂ)
    (hM : ∀ r x, hsSq (M r x) = 1) (hN : ∀ r y, hsSq (N r y) = 1)
    (P : R → Fin (x+1) → POVM m (Fin (a+1))) (Q : R → Fin (y+1) → POVM n (Fin (b+1)))
    {eA eB : ℝ}
    (hA : ρ.avg (fun r => G.questionLaw.avg (fun z => hsSq (D r z-M r z.1))) ≤ eA)
    (hB : ρ.avg (fun r => G.questionLaw.avg (fun z => hsSq (D r z-N r z.2))) ≤ eB)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ρ.avg (fun r => G.questionLaw.avg (fun z => payoff (D r z) (P r z.1) (Q r z.2) (G.accepts z.1 z.2))) ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (4*(eA+eB))) +
        2*Real.sqrt eA+eA := by
  let D' := fun z => weightedBlock ρ.weight (fun r => D r z)
  let M' := fun x => weightedBlock ρ.weight (fun r => M r x)
  let N' := fun y => weightedBlock ρ.weight (fun r => N r y)
  have hm : ∀ x, hsSq (M' x) = 1 := by
    intro x
    simp only [M', hsSq_weightedBlock _ ρ.nonneg, hM, mul_one, ρ.total]
  have hn : ∀ y, hsSq (N' y) = 1 := by
    intro y
    simp only [N', hsSq_weightedBlock _ ρ.nonneg, hN, mul_one, ρ.total]
  have ha : G.questionLaw.avg (fun z => hsSq (D' z-M' z.1)) ≤ eA := by
    simp only [D', M', hsSq_weightedBlock_sub _ ρ.nonneg]
    change G.questionLaw.avg (fun z => ρ.avg (fun r => hsSq (D r z-M r z.1))) ≤ _
    rw [avg_comm]; exact hA
  have hb : G.questionLaw.avg (fun z => hsSq (D' z-N' z.2)) ≤ eB := by
    simp only [D', N', hsSq_weightedBlock_sub _ ρ.nonneg]
    change G.questionLaw.avg (fun z => ρ.avg (fun r => hsSq (D r z-N r z.2))) ≤ _
    rw [avg_comm]; exact hB
  have hh := rounding_value_rect G D' M' N' hm hn
    (fun x => POVM.blocks (fun r => P r x)) (fun y => POVM.blocks (fun r => Q r y)) ha hb hε hε1
  simp only [D', payoff_weightedBlock _ ρ.nonneg] at hh
  change G.questionLaw.avg (fun z => ρ.avg (fun r => payoff (D r z) (P r z.1) (Q r z.2) (G.accepts z.1 z.2))) ≤ _ at hh
  rw [avg_comm] at hh
  exact hh
end QuantumSampling
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {R : Type u_R} [Fintype R] [Nonempty R]
end ThresholdParallelRepetition.FiniteProbability.Law

end

noncomputable section
namespace ThresholdParallelRepetition
lemma rounding_loss_small {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (_hτ : 0 ≤ τ)
    (hsmall : τ ≤ δ^8/(2:ℝ)^80) :
    4*Real.sqrt (2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ)) +
      2*Real.sqrt (4*τ)+4*τ ≤ δ/4 := by
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have h24 : δ^4 ≤ δ^2 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h48 : δ^8 ≤ δ^4 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have hs32 : Real.sqrt (32*τ) ≤ δ^4/(2:ℝ)^36 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hterm : (12/(δ^2/1024))*Real.sqrt (32*τ) ≤ δ^2/2048 := by
    have hmul := mul_le_mul_of_nonneg_left hs32 (show 0 ≤ 12/(δ^2/1024) by positivity)
    have he : (12/(δ^2/1024))*(δ^4/(2:ℝ)^36) = (3/(2:ℝ)^24)*δ^2 := by
      field_simp; ring
    rw [he] at hmul
    nlinarith
  have hinner : 2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ) ≤ δ^2/1024 := by
    nlinarith
  have hsout : Real.sqrt (2*(δ^2/1024)^2+(12/(δ^2/1024))*Real.sqrt (32*τ)) ≤ δ/32 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hs4 : Real.sqrt (4*τ) ≤ δ/64 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have ht4 : 4*τ ≤ δ/32 := by nlinarith
  linarith
end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {I R m n : Type} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (S : EventSystem (Fin (x+1)) (Fin (y+1)) I R m n)
  (hμ : S.μ = G.questionLaw)
  (T : Refinement S (Fin (a+1)) (Fin (b+1)))

include hμ
lemma conditional_rounding_bound (hl : 0 < S.l.length) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤
      entangledValue G + 4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (32*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)))) +
        2*Real.sqrt (4*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)))+
          4*(Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)) := by
  have : Nonempty (Fin S.l.length) := ⟨⟨0,hl⟩⟩
  let E : Matrix ((S.J×m)×(R×Profile I (Fin (x+1)) (Fin (y+1))))
      ((S.J×n)×(R×Profile I (Fin (x+1)) (Fin (y+1)))) ℂ :=
    basisState (Classical.arbitrary _) (Classical.arbitrary _)
  have hE : hsSq E = 1 := hsSq_basisState _ _
  let τ := Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ)
  have hb := S.normalized_error_bounds E hE
  have hA : (uniform (R := Fin S.l.length)).avg (fun j => G.questionLaw.avg
      (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*τ := by
    rw [← hμ, uniform_avg, Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 1/(S.l.length : ℝ) by positivity)
    exact hh.trans_eq (by dsimp only [τ]; ring)
  have hB : (uniform (R := Fin S.l.length)).avg (fun j => G.questionLaw.avg
      (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*τ := by
    rw [← hμ, uniform_avg, Fintype.card_fin]
    have hh := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 1/(S.l.length : ℝ) by positivity)
    exact hh.trans_eq (by dsimp only [τ]; ring)
  have hr := rounding_value_modes G uniform S.D (fun j => S.M j E) (fun j => S.N j E)
    (fun j => S.M_unit j E hE) (fun j => S.N_unit j E hE) (T.P 0) (T.Q 0) hA hB hε hε1
  rw [← hμ] at hr
  simp only [T.payoff_D_eq_score, uniform_avg, Fintype.card_fin] at hr
  have he : 4*(4*τ+4*τ)=32*τ := by ring
  simpa only [he, τ] using hr

lemma conditional_rounding_small (hl : 0 < S.l.length) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (1/(S.l.length : ℝ))*∑ j : Fin S.l.length, T.score S.l[j.val] G.accepts ≤ entangledValue G+δ/4 := by
  have hn : 0 ≤ Real.log ((Fintype.card R : ℝ)/S.p) := by
    have he := S.raw_error_bounds.1
    have hz : 0 ≤ ∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)) :=
      Finset.sum_nonneg (fun j _ => S.μ.avg_nonneg (fun q => hsSq_nonneg _))
    exact hz.trans he
  have ht : 0 ≤ Real.log ((Fintype.card R : ℝ)/S.p)/(S.l.length : ℝ) := div_nonneg hn (Nat.cast_nonneg _)
  have he0 : 0 < δ^2/1024 := by positivity
  have he1 : δ^2/1024 ≤ 1 := by nlinarith
  have hh := conditional_rounding_bound G S hμ T hl he0 he1
  have hnum := rounding_loss_small hδ hδ1 ht hsmall
  linarith
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law OperatorEntropy
variable {m : Type u_m} {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} {T : Type u_T} {U : Type u_U} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype A] [Fintype B] [Fintype R] [Fintype T] [Fintype U]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.ConditionedStep ----
namespace OAI

universe u_I

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure

lemma sum_fin_get_toList {I : Type u_I} [DecidableEq I] (c : Finset I) (f : I → ℝ) :
    (∑ j : Fin c.toList.length, f c.toList[j.val]) = ∑ i ∈ c, f i := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map, Finset.sum_map_toList]

namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

omit [Nonempty I] in
lemma fresh_sum_bound (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (∑ i ∈ cᶜ, M.mass (insert i c)) ≤
      (entangledValue G+δ/4)*M.mass c*((Fintype.card I-c.card : ℕ) : ℝ) := by
  have hl : 0 < (M.exposure c hp).l.length := by
    change 0 < cᶜ.toList.length
    simp only [Finset.length_toList, Finset.card_compl]
    omega
  have hs : Real.log ((Fintype.card (Records (A := Fin (a+1)) (B := Fin (b+1)) c) : ℝ)/(M.exposure c hp).p)/
      ((M.exposure c hp).l.length : ℝ) ≤ δ^8/(2:ℝ)^80 := by
    simpa only [exposure, card_records, Fintype.card_fin, Nat.cast_pow, Finset.length_toList, Finset.card_compl] using hsmall
  have hh := conditional_rounding_small G (M.exposure c hp) hμ (M.refinement c hp) hl hδ hδ1 hs
  rw [← hV] at hh
  simp only [M.score_eq_mass_ratio] at hh
  change (1/(cᶜ.toList.length : ℝ))*∑ j : Fin cᶜ.toList.length,
    M.mass (insert cᶜ.toList[j.val] c)/M.mass c ≤ _ at hh
  rw [sum_fin_get_toList cᶜ (fun i => M.mass (insert i c)/M.mass c), ← Finset.sum_div, Finset.length_toList, Finset.card_compl] at hh
  have hn : 0 < ((Fintype.card I-c.card : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hc
  rw [one_div, inv_mul_eq_div] at hh
  have hm := (div_le_iff₀ hp).mp ((div_le_iff₀ hn).mp hh)
  nlinarith

lemma good_event_step (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : (c.card : ℝ) ≤ δ*(Fintype.card I : ℝ)/4)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤ (entangledValue G+δ/2)*M.mass c := by
  have hf := M.fresh_sum_bound G hμ hV c hp hc hδ hδ1 hsmall
  have hcBound : (∑ i ∈ c, M.mass (insert i c)) ≤ (c.card : ℝ)*M.mass c := by
    calc
      _ ≤ ∑ _i ∈ c, M.mass c := Finset.sum_le_sum (fun i _ => M.mass_insert_le c i)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hv : 0 ≤ entangledValue G+δ/4 := by linarith [entangledValue_nonneg G]
  have hcard : ((Fintype.card I-c.card : ℕ) : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Nat.sub_le (Fintype.card I) c.card
  have hsum := add_le_add hcBound (hf.trans (mul_le_mul_of_nonneg_left hcard (mul_nonneg hv hp.le)))
  rw [Finset.sum_add_sum_compl] at hsum
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [uniform_avg, one_div, inv_mul_eq_div]
  apply (div_le_iff₀ hn).mpr
  have hsz := mul_le_mul_of_nonneg_right hsize hp.le
  nlinarith

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

end ThresholdParallelRepetition

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.RepeatedModel
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling FiniteProbability Law MixedExposure


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.RepeatedModel.good_event_step := @_root_.OAI.ThresholdParallelRepetition.RepeatedModel.good_event_step
