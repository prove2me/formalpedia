-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.step_right
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:18:37.002997+00:00
-- url     : https://prove2.me/submissions/b5020c9f-c2da-4a08-850a-12f882adc035

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/MixedExposure.lean:L77-L136
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MixedExposure.step_right. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_left
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_right
import Theorems.Thm_OAI_ThresholdParallelRepetition_Resolvent_weighted_distance_jensen

-- ---- from OAI.Probability.EntangledGames.Purification ----
namespace OAI

universe u_n u_α u_m u_p u_J u_R

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter Set
namespace ThresholdParallelRepetition.Resolvent
attribute [local instance] matrixContinuousENorm matrixPreorder matrixClosedIci rectContinuousENorm
variable {n : Type u_n} [Fintype n] [DecidableEq n]

variable {J : Type u_J} [Fintype J] [DecidableEq J]

lemma finitePurification_distance (A : J → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (j k : J) :
    (finitePurification A j - finitePurification A k)ᴴ *
      (finitePurification A j - finitePurification A k) =
      ∫ s : ℝ in Ioi 0, (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) := by
  conv_lhs => rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  have hd (s : ℝ) :
      (purificationKernel (A j) s - purificationKernel (A k) s)ᴴ *
        (purificationKernel (A j) s - purificationKernel (A k) s) =
      ((purificationKernel (A j) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A j) s)ᴴ * purificationKernel (A k) s) -
      ((purificationKernel (A k) s)ᴴ * purificationKernel (A j) s -
        (purificationKernel (A k) s)ᴴ * purificationKernel (A k) s) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp_rw [hd]
  erw [integral_sub ((kernel_cross_integrable (hA j) (hA j)).sub
      (kernel_cross_integrable (hA j) (hA k)))
      ((kernel_cross_integrable (hA k) (hA j)).sub (kernel_cross_integrable (hA k) (hA k))),
    integral_sub (kernel_cross_integrable (hA j) (hA j)) (kernel_cross_integrable (hA j) (hA k)),
    integral_sub (kernel_cross_integrable (hA k) (hA j)) (kernel_cross_integrable (hA k) (hA k))]
  simp only [finitePurification_product A hA]

lemma finitePurification_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (e : R → J) (w : R → ℝ) (k : J)
    (hw0 : ∀ r, 0 ≤ w r) (hw : ∑ r, w r = 1)
    (hmean : ∑ r, w r • A (e r) = A k) :
    (∑ r, w r • ((finitePurification A (e r) - finitePurification A k)ᴴ *
      (finitePurification A (e r) - finitePurification A k))) ≤
      (∑ r, w r • effectEntropy (A (e r))) - effectEntropy (A k) := by
  simp_rw [finitePurification_distance A hA]
  exact weighted_distance_jensen (A ∘ e) w (A k) (fun r => hA (e r))
    (fun r => hA1 (e r)) (hA k) (hA1 k) hw0 hw hmean

end ThresholdParallelRepetition.Resolvent

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
lemma prob_sub_right (C : Matrix m n ℂ) (A : Matrix m m ℂ) (B B' : Matrix n n ℂ) :
    prob C A (B-B') = prob C A B - prob C A B' := by
  simp only [prob, eval_eq_trace, Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

omit [DecidableEq n] [DecidableEq q] in
lemma prob_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (Kᴴ*K) (Lᴴ*L) = hsSq (K*D*Lᵀ) := by
  simpa only [Matrix.mul_one, prob_one] using prob_pullback D K L (1 : Matrix m m ℂ) (1 : Matrix p p ℂ)
end FilterMass

open Filter Topology
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

lemma avg_sub {F : Type u_F} [AddCommGroup F] [Module ℝ F]
    (p : Law α) (f g : α → F) :
    p.avg (fun x => f x-g x) = p.avg f-p.avg g := by
  simp only [avg, smul_sub, Finset.sum_sub_distrib]
lemma avg_linear (p : Law α) (f : α → E) {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) : L (p.avg f) = p.avg (fun x => L (f x)) := by
  simp [avg]

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

variable {m : Type u_m} [Fintype m] [DecidableEq m]

omit [DecidableEq n] [DecidableEq m] in
lemma prob_mono_right (C : Matrix m n ℂ) {A : Matrix m m ℂ} {B B' : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B ≤ B') : prob C A B ≤ prob C A B' := by
  have h := prob_nonneg (C := C) hA (show (B'-B).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB))
  rw [prob_sub_right] at h
  linarith

end OperatorEntropy
end ThresholdParallelRepetition

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

omit [Fintype I] [DecidableEq X] in
lemma right_ignoresRight (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E) :
    IgnoresRight (μ.right y₀ i f) i := by
  intro z y
  simp only [right, updateRight, Function.update_self]
  congr 1
  funext y'
  simp [Function.update_idem]

section Linear
variable {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
omit [Fintype I] [DecidableEq Y] in
lemma left_linear (μ : Law (X×Y)) (x₀ : X) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.left x₀ i f z) = μ.left x₀ i (fun q => L (f q)) z := avg_linear _ _ _
omit [Fintype I] [DecidableEq X] in
lemma right_linear (μ : Law (X×Y)) (y₀ : Y) (i : I)
    (f : Profile I X Y → E) (L : E →ₗ[ℝ] F) (z : Profile I X Y) :
    L (μ.right y₀ i f z) = μ.right y₀ i (fun q => L (f q)) z := avg_linear _ _ _

omit [DecidableEq Y] in
lemma pi_left_pairing (μ : Law (X×Y)) (x₀ : X) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.left x₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.left x₀ i f z)) =
      μ.left x₀ i (fun z => L z (f z)) := by
    funext z
    rw [left_linear]
    unfold left
    congr 1
    funext x
    simp only [hL z x]
  rw [he, pi_avg_left]

omit [DecidableEq X] in
lemma pi_right_pairing (μ : Law (X×Y)) (y₀ : Y) (i : I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.right y₀ i f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  have he : (fun z => L z (μ.right y₀ i f z)) =
      μ.right y₀ i (fun z => L z (f z)) := by
    funext z
    rw [right_linear]
    unfold right
    congr 1
    funext y
    simp only [hL z y]
  rw [he, pi_avg_right]
end Linear

section Folds

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

-- ---- from OAI.Probability.EntangledGames.EffectExposure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_R u_n u_X u_Y u_I u_A u_B u_m u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling Resolvent OperatorEntropy FiniteProbability

namespace FiniteProbability.Law
variable {R : Type u_R} {n : Type u_n} [Fintype R] [Fintype n] [DecidableEq n]
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq I]
end FiniteProbability.Law

namespace QuantumSampling.POVM
variable {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} [Fintype n] [DecidableEq n] [Fintype A] [Fintype B] [Fintype R]
end QuantumSampling.POVM

namespace OperatorEntropy
variable {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end OperatorEntropy

namespace Resolvent
variable {J : Type u_J} {n : Type u_n} [Fintype J] [Nonempty J] [DecidableEq J] [Fintype n] [DecidableEq n]

lemma commonMap_jensen {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) :
    p.avg (fun r => (commonMap A (F r)-commonMap A (p.avg F))ᴴ *
      (commonMap A (F r)-commonMap A (p.avg F))) ≤
      p.avg (fun r => effectEntropy (F r)) - effectEntropy (p.avg F) := by
  have h := finitePurification_jensen A hA hA1 (fun r => effectIndex A (F r)) p.weight
    (effectIndex A (p.avg F)) p.nonneg p.total (by
      simp only [effectIndex_eq A (hF _), effectIndex_eq A hmean]; rfl)
  simp only [effectIndex_eq A (hF _), effectIndex_eq A hmean] at h
  exact h

variable {m : Type u_m} {K : Type u_K} [Fintype m] [DecidableEq m] [Fintype K] [DecidableEq K]
omit [DecidableEq m] in
lemma commonMap_error_right {R : Type u_R} [Fintype R]
    (A : J → Matrix n n ℂ) (hA : ∀ j, (A j).PosSemidef) (hA1 : ∀ j, A j ≤ 1)
    (p : Law R) (F : R → Matrix n n ℂ) (hF : ∀ r, F r ∈ Set.range A)
    (hmean : p.avg F ∈ Set.range A) (C : Matrix m n ℂ) (L : Matrix K m ℂ) :
    p.avg (fun r => hsSq (L*C*(commonMap A (F r)-commonMap A (p.avg F))ᵀ)) ≤
      p.avg (fun r => prob C (Lᴴ*L) (effectEntropy (F r))) -
        prob C (Lᴴ*L) (effectEntropy (p.avg F)) := by
  have h := prob_mono_right C (Matrix.posSemidef_conjTranspose_mul_self L)
    (commonMap_jensen A hA hA1 p F hF hmean)
  rw [prob_sub_right] at h
  have he (T : R → Matrix n n ℂ) : prob C (Lᴴ*L) (p.avg T) =
      p.avg (fun r => prob C (Lᴴ*L) (T r)) := p.avg_linear T (probRight C (Lᴴ*L))
  rw [he, he] at h
  convert h using 1
  apply congrArg p.avg
  funext r
  exact (prob_gram C L _).symm
end Resolvent

end ThresholdParallelRepetition

end

end OAI

-- ---- from OAI.Probability.EntangledGames.MixedExposure ----
namespace OAI

universe u_X u_Y u_I u_m u_n u_J u_K

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} {J : Type u_J} {K : Type u_K} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype K] [DecidableEq K] [Nonempty K]

lemma step_right (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (i : I)
    (C : Matrix m n ℂ) (A : J → Matrix m m ℂ) (B : K → Matrix n n ℂ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ j, (B j).PosSemidef) (hB1 : ∀ j, B j ≤ 1)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ z, F z ∈ Set.range A) (hH : ∀ z, H z ∈ Set.range B)
    (hH1 : ∀ z, μ.right y₀ i H z ∈ Set.range B)
    (hFi : IgnoresRight F i) (hHi : IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθ : ∀ z, 0 ≤ θ z)
    (hθL : IgnoresLeft θ i) (hθR : IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * hsSq
      (commonMap A (F z)*C*(commonMap B (H z) - commonMap B (μ.right y₀ i H z))ᵀ)) ≤
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.left x₀ i F z) (effectEntropy (H z))) -
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (effectEntropy (μ.right y₀ i H z))) := by
  let ρ := pi (fun _ : I => μ)
  let T := μ.right y₀ i H
  let e : Profile I X Y → ℝ := fun z => θ z * hsSq
    (commonMap A (F z)*C*(commonMap B (H z)-commonMap B (T z))ᵀ)
  have hTi : IgnoresRight T i := right_ignoresRight μ y₀ i H
  have hstep (z : Profile I X Y) : μ.right y₀ i e z ≤
      θ z * (prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) -
        prob C (F z) (effectEntropy (T z))) := by
    have h := commonMap_error_right B hB hB1 (μ.givenFirst y₀ (z i).1)
      (fun y => H (updateRight z i y)) (fun y => hH _) (hH1 z) C (commonMap A (F z))
    rw [commonMap_gram A hA (hF z)] at h
    have hl : μ.right y₀ i e z = θ z *
        (μ.givenFirst y₀ (z i).1).avg (fun y => hsSq
          (commonMap A (F z)*C*(commonMap B (H (updateRight z i y))-commonMap B (T z))ᵀ)) := by
      simp only [right, e, hθR z, hTi z, hFi z, Law.avg, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hl]
    apply mul_le_mul_of_nonneg_left _ (hθ z)
    have heq := (μ.givenFirst y₀ (z i).1).avg_linear
      (fun y => effectEntropy (H (updateRight z i y))) (probRight C (F z))
    change prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) = _ at heq
    rw [heq]
    exact h
  have havg := ρ.avg_mono hstep
  have hPairR : ρ.avg (fun z => θ z * prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z)) =
      ρ.avg (fun z => θ z * prob C (F z) (effectEntropy (H z))) := by
    apply pi_right_pairing μ y₀ i (fun z => effectEntropy (H z))
      (fun z => θ z • probRight C (F z))
    intro z y
    simp only [hθR z, hFi z]
  have hPairL : ρ.avg (fun z => θ z * prob C (μ.left x₀ i F z) (effectEntropy (H z))) =
      ρ.avg (fun z => θ z * prob C (F z) (effectEntropy (H z))) := by
    apply pi_left_pairing μ x₀ i F (fun z => θ z • probLeft C (effectEntropy (H z)))
    intro z x
    simp only [hθL z, hHi z]
  have he : ρ.avg (μ.right y₀ i e) = ρ.avg e := pi_avg_right μ y₀ i e
  rw [he] at havg
  have hr : ρ.avg (fun z => θ z * (prob C (F z) (μ.right y₀ i (fun z => effectEntropy (H z)) z) -
        prob C (F z) (effectEntropy (T z)))) =
      ρ.avg (fun z => θ z*prob C (μ.left x₀ i F z) (effectEntropy (H z))) -
      ρ.avg (fun z => θ z*prob C (F z) (effectEntropy (T z))) := by
    simp only [mul_sub, Law.avg_sub]
    rw [hPairR, hPairL]
  exact havg.trans_eq hr
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype m] [Fintype n]

end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law


theorem solution.{u_X,u_Y,u_I,u_m,u_n,u_J,u_K} : type_of% @_root_.OAI.ThresholdParallelRepetition.MixedExposure.step_right.{u_X,u_Y,u_I,u_m,u_n,u_J,u_K} := @_root_.OAI.ThresholdParallelRepetition.MixedExposure.step_right.{u_X,u_Y,u_I,u_m,u_n,u_J,u_K}
