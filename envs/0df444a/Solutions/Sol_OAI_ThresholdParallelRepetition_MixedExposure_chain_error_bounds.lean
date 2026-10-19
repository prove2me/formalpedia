-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.chain_error_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:20:56.118989+00:00
-- url     : https://prove2.me/submissions/f7109c5e-c803-4409-b501-7d7cc530808e

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureChain.lean:L190-L279
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MixedExposure.chain_error_bounds. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_left
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_pi_avg_right
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_step_left
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_step_right
import Theorems.Thm_OAI_ThresholdParallelRepetition_OperatorEntropy_effectEntropy_nonpos
import Theorems.Thm_OAI_ThresholdParallelRepetition_OperatorEntropy_functional_entropy_lower
import Theorems.Thm_OAI_ThresholdParallelRepetition_ScalarEntropy_weighted_negMulLog_le

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
lemma prob_mono_left (C : Matrix m n ℂ) {A A' : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hB : B.PosSemidef) (hA : A ≤ A') : prob C A B ≤ prob C A' B := by
  have h := prob_nonneg (C := C) (show (A'-A).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hA)) hB
  rw [prob_sub_left] at h
  linarith
omit [DecidableEq n] [DecidableEq m] in
lemma prob_mono_right (C : Matrix m n ℂ) {A : Matrix m m ℂ} {B B' : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B ≤ B') : prob C A B ≤ prob C A B' := by
  have h := prob_nonneg (C := C) hA (show (B'-B).PosSemidef from Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB))
  rw [prob_sub_right] at h
  linarith

lemma prob_entropy_left_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hB1 : B ≤ 1) :
    -prob C (effectEntropy A) B ≤ Real.negMulLog (prob C A B) := by
  apply functional_entropy_lower (probLeft C B) (fun T hT => prob_nonneg hT hB) _ hA
  exact ((prob_mono_right C Matrix.PosSemidef.one hB1).trans_eq (prob_one C)).trans hC

lemma prob_entropy_right_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (hB : B.PosSemidef) :
    -prob C A (effectEntropy B) ≤ Real.negMulLog (prob C A B) := by
  apply functional_entropy_lower (probRight C A) (fun T hT => prob_nonneg hA hT) _ hB
  exact ((prob_mono_left C Matrix.PosSemidef.one hA1).trans_eq (prob_one C)).trans hC

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

omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] in
lemma updateLeft_right_comm (z : Profile I X Y) (i j : I) (x : X) (y : Y) :
    updateLeft (updateRight z j y) i x = updateRight (updateLeft z i x) j y := by
  by_cases hij : i = j
  · subst j; simp [updateLeft, updateRight]
  · simp only [updateLeft, updateRight, Function.update_of_ne hij,
      Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm (Ne.symm hij) _ _ z

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
omit [DecidableEq Y] in
lemma pi_lefts_pairing (μ : Law (X×Y)) (x₀ : X) (l : List I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ i ∈ l, IgnoresLeft L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.lefts x₀ l f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (pi _).avg (fun z => L z (μ.left x₀ i (μ.lefts x₀ l f) z)) = _
    rw [pi_left_pairing μ x₀ i _ L (hL i (List.mem_cons_self))]
    exact ih (fun j hj => hL j (List.mem_cons_of_mem i hj))

omit [DecidableEq X] in
lemma pi_rights_pairing (μ : Law (X×Y)) (y₀ : Y) (l : List I) (f : Profile I X Y → E)
    (L : Profile I X Y → E →ₗ[ℝ] F) (hL : ∀ i ∈ l, IgnoresRight L i) :
    (pi (fun _ : I => μ)).avg (fun z => L z (μ.rights y₀ l f z)) =
      (pi (fun _ : I => μ)).avg (fun z => L z (f z)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (pi _).avg (fun z => L z (μ.right y₀ i (μ.rights y₀ l f) z)) = _
    rw [pi_right_pairing μ y₀ i _ L (hL i (List.mem_cons_self))]
    exact ih (fun j hj => hL j (List.mem_cons_of_mem i hj))
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
lemma avg_matrix_mono (p : Law R) {A B : R → Matrix n n ℂ} (h : ∀ r, A r ≤ B r) :
    p.avg A ≤ p.avg B := by
  unfold avg
  exact Finset.sum_le_sum (fun r _ => smul_le_smul_of_nonneg_left (h r) (p.nonneg r))
lemma avg_matrix_le (p : Law R) {A : R → Matrix n n ℂ} {B : Matrix n n ℂ}
    (h : ∀ r, A r ≤ B) : p.avg A ≤ B := by
  simpa only [avg_const] using p.avg_matrix_mono h

variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq I]
omit [DecidableEq Y] in
lemma lefts_le (μ : Law (X×Y)) (x₀ : X) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) {B : Matrix n n ℂ} (hf : ∀ z, f z ≤ B) :
    ∀ z, μ.lefts x₀ l f z ≤ B := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_matrix_le _ (fun _ => ih _)
omit [DecidableEq X] in
lemma rights_le (μ : Law (X×Y)) (y₀ : Y) (l : List I)
    (f : Profile I X Y → Matrix n n ℂ) {B : Matrix n n ℂ} (hf : ∀ z, f z ≤ B) :
    ∀ z, μ.rights y₀ l f z ≤ B := by
  induction l with
  | nil => exact hf
  | cons i l ih => intro z; exact avg_matrix_le _ (fun _ => ih _)
end FiniteProbability.Law

namespace QuantumSampling.POVM
variable {n : Type u_n} {A : Type u_A} {B : Type u_B} {R : Type u_R} [Fintype n] [DecidableEq n] [Fintype A] [Fintype B] [Fintype R]
end QuantumSampling.POVM

namespace OperatorEntropy
variable {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
lemma potential_left_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hH : ∀ r, (H r).PosSemidef) (hH1 : ∀ r, H r ≤ 1)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ r, w r ≤ d) (hp : 0 < p)
    (hm : ∑ r, w r*prob C (F r) (H r) = p) :
    -p*Real.log (d/p) ≤ ∑ r, w r * prob C (effectEntropy (F r)) (H r) := by
  have h := ScalarEntropy.weighted_negMulLog_le w (fun r => prob C (F r) (H r)) hw
    (fun r => prob_nonneg (hF r) (hH r)) hd hs hp hm
  have h' : -(∑ r, w r*prob C (effectEntropy (F r)) (H r)) ≤
      ∑ r, w r*Real.negMulLog (prob C (F r) (H r)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (prob_entropy_left_lower C hC (hF r) (hH r) (hH1 r)) (hw r))
  linarith
lemma potential_right_lower (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hF1 : ∀ r, F r ≤ 1) (hH : ∀ r, (H r).PosSemidef)
    {d p : ℝ} (hd : 0 < d) (hs : ∑ r, w r ≤ d) (hp : 0 < p)
    (hm : ∑ r, w r*prob C (F r) (H r) = p) :
    -p*Real.log (d/p) ≤ ∑ r, w r * prob C (F r) (effectEntropy (H r)) := by
  have h := ScalarEntropy.weighted_negMulLog_le w (fun r => prob C (F r) (H r)) hw
    (fun r => prob_nonneg (hF r) (hH r)) hd hs hp hm
  have h' : -(∑ r, w r*prob C (F r) (effectEntropy (H r))) ≤
      ∑ r, w r*Real.negMulLog (prob C (F r) (H r)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun r _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left
        (prob_entropy_right_lower C hC (hF r) (hF1 r) (hH r)) (hw r))
  linarith
omit [DecidableEq n] in
lemma potential_left_nonpos (C : Matrix m n ℂ)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hF1 : ∀ r, F r ≤ 1) (hH : ∀ r, (H r).PosSemidef) :
    (∑ r, w r * prob C (effectEntropy (F r)) (H r)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r _
  apply mul_nonpos_of_nonneg_of_nonpos (hw r)
  simpa only [prob, eval_eq_trace, Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero,
    Complex.zero_re] using prob_mono_left C (hH r) (effectEntropy_nonpos (hF r) (hF1 r))
omit [DecidableEq m] in
lemma potential_right_nonpos (C : Matrix m n ℂ)
    (w : R → ℝ) (hw : ∀ r, 0 ≤ w r) (F : R → Matrix m m ℂ) (H : R → Matrix n n ℂ)
    (hF : ∀ r, (F r).PosSemidef) (hH : ∀ r, (H r).PosSemidef) (hH1 : ∀ r, H r ≤ 1) :
    (∑ r, w r * prob C (F r) (effectEntropy (H r))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro r _
  apply mul_nonpos_of_nonneg_of_nonpos (hw r)
  simpa only [prob, eval_eq_trace, Matrix.transpose_zero, Matrix.mul_zero, Matrix.trace_zero,
    Complex.zero_re] using prob_mono_right C (hF r) (effectEntropy_nonpos (hH r) (hH1 r))
end OperatorEntropy

namespace Resolvent
variable {J : Type u_J} {n : Type u_n} [Fintype J] [Nonempty J] [DecidableEq J] [Fintype n] [DecidableEq n]

variable {m : Type u_m} {K : Type u_K} [Fintype m] [DecidableEq m] [Fintype K] [DecidableEq K]
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

lemma mixed_pairing (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l r : List I)
    (hlr : ∀ i ∈ l, i ∉ r) (C : Matrix m n ℂ)
    (F : Profile I X Y → Matrix m m ℂ) (H : Profile I X Y → Matrix n n ℂ)
    (hF : ∀ i ∈ r, IgnoresRight F i) (hH : ∀ i ∈ l, IgnoresLeft H i)
    (θ : Profile I X Y → ℝ) (hθL : ∀ i ∈ l, IgnoresLeft θ i) (hθR : ∀ i ∈ r, IgnoresRight θ i) :
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (μ.lefts x₀ l F z) (μ.rights y₀ r H z)) =
    (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (H z)) := by
  calc
    _ = (pi (fun _ : I => μ)).avg (fun z => θ z * prob C (F z) (μ.rights y₀ r H z)) := by
      apply pi_lefts_pairing μ x₀ l F (fun z => θ z • probLeft C (μ.rights y₀ r H z))
      intro i hi z x
      simp only [hθL i hi z, rights_ignoresLeft_notMem μ y₀ r (hlr i hi) (hH i hi) z]
    _ = _ := by
      apply pi_rights_pairing μ y₀ r H (fun z => θ z • probRight C (F z))
      intro i hi z y
      simp only [hθR i hi z, hF i hi z]

end ThresholdParallelRepetition.MixedExposure

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

omit [DecidableEq m] [DecidableEq n] in
lemma chain_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (j : ℕ) :
    (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z *
      prob C (chainLeft μ x₀ l F j r z) (chainRight μ y₀ l H j r z))) =
    ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z)) := by
  apply Finset.sum_congr rfl
  intro r _
  apply mixed_pairing μ x₀ y₀ _ _ (list_suffix_prefix_disjoint l hN j) C (F r) (H r)
    (fun i _ => hF r i) (fun i _ => hH r i) (θ r)
  · exact fun i hi => hθL r i (List.mem_of_mem_drop hi)
  · exact fun i hi => hθR r i (List.mem_of_mem_take (List.mem_reverse.mp hi))
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law
variable {R : Type u_R} {Z : Type u_Z} {m : Type u_m} {n : Type u_n} [Fintype R] [Nonempty R] [Fintype Z]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

omit [Nonempty R] in
lemma tested_weight_sum_le (ρ : Law Z) (θ : R → Z → ℝ) (hθ1 : ∀ r z, θ r z ≤ 1) :
    (∑ t : R×Z, ρ.weight t.2 * θ t.1 t.2) ≤ Fintype.card R := by
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _r : R, ∑ z, ρ.weight z := by
      apply Finset.sum_le_sum; intro r _
      exact Finset.sum_le_sum (fun z _ => by nlinarith [ρ.nonneg z, hθ1 r z])
    _ = _ := by simp only [ρ.total, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma averaged_potential_left_bounds (ρ : Law Z) (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (θ : R → Z → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (F : R → Z → Matrix m m ℂ) (H : R → Z → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    {p : ℝ} (hp : 0 < p) (hm : (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    -p*Real.log ((Fintype.card R : ℝ)/p) ≤
      ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (F r z)) (H r z)) ∧
    (∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (F r z)) (H r z))) ≤ 0 := by
  have hmass : ∑ t : R×Z, (ρ.weight t.2*θ t.1 t.2)*prob C (F t.1 t.2) (H t.1 t.2) = p := by
    simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using hm
  have h0 := potential_left_lower C hC (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hH _ _) (fun t => hH1 _ _)
    (Nat.cast_pos.mpr (Fintype.card_pos)) (tested_weight_sum_le ρ θ hθ1) hp hmass
  have h1 := potential_left_nonpos C (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hF1 _ _) (fun t => hH _ _)
  simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using And.intro h0 h1

lemma averaged_potential_right_bounds (ρ : Law Z) (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (θ : R → Z → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (F : R → Z → Matrix m m ℂ) (H : R → Z → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    {p : ℝ} (hp : 0 < p) (hm : (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    -p*Real.log ((Fintype.card R : ℝ)/p) ≤
      ∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (effectEntropy (H r z))) ∧
    (∑ r, ρ.avg (fun z => θ r z*prob C (F r z) (effectEntropy (H r z)))) ≤ 0 := by
  have hmass : ∑ t : R×Z, (ρ.weight t.2*θ t.1 t.2)*prob C (F t.1 t.2) (H t.1 t.2) = p := by
    simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using hm
  have h0 := potential_right_lower C hC (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hF1 _ _) (fun t => hH _ _)
    (Nat.cast_pos.mpr (Fintype.card_pos)) (tested_weight_sum_le ρ θ hθ1) hp hmass
  have h1 := potential_right_nonpos C (fun t : R×Z => ρ.weight t.2*θ t.1 t.2)
    (fun t => mul_nonneg (ρ.nonneg _) (hθ _ _)) (fun t => F t.1 t.2) (fun t => H t.1 t.2)
    (fun t => hF _ _) (fun t => hH _ _) (fun t => hH1 _ _)
  simpa only [Fintype.sum_prod_type, Law.avg, smul_eq_mul, mul_assoc] using And.intro h0 h1

lemma fin_telescope_bound {N : ℕ} (U : ℕ → ℝ) (e : Fin N → ℝ) (L : ℝ)
    (hstep : ∀ i, e i ≤ U (i+1)-U i) (h0 : -L ≤ U 0) (hN : U N ≤ 0) :
    ∑ i, e i ≤ L := by
  calc
    _ ≤ ∑ i : Fin N, (U (i+1)-U i) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = U N-U 0 := by rw [Fin.sum_univ_eq_sum_range (fun i => U (i+1)-U i), Finset.sum_range_sub]
    _ ≤ L := by linarith

lemma fin_telescope_bound_rev {N : ℕ} (U : ℕ → ℝ) (e : Fin N → ℝ) (L : ℝ)
    (hstep : ∀ i, e i ≤ U i-U (i+1)) (h0 : U 0 ≤ 0) (hN : -L ≤ U N) :
    ∑ i, e i ≤ L := by
  calc
    _ ≤ ∑ i : Fin N, (U i-U (i+1)) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = U 0-U N := by rw [Fin.sum_univ_eq_sum_range (fun i => U i-U (i+1)), Finset.sum_range_sub']
    _ ≤ L := by linarith
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

lemma chain_error_bounds (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (hC : hsSq C ≤ 1)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hF1 : ∀ r z, F r z ≤ 1)
    (hH : ∀ r z, (H r z).PosSemidef) (hH1 : ∀ r z, H r z ≤ 1)
    (hFlocal : ∀ r i, IgnoresRight (F r) i) (hHlocal : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z) (hθ1 : ∀ r z, θ r z ≤ 1)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    {p : ℝ} (hp : 0 < p)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * prob C (F r z) (H r z))) = p) :
    let A := chainLeftFamily μ x₀ l F
    let B := chainRightFamily μ y₀ l H
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      ((commonMap A (chainLeft μ x₀ l F (j+1) r z)-commonMap A (chainLeft μ x₀ l F j r z))*C*
        (commonMap B (chainRight μ y₀ l H j r z))ᵀ))) ≤ p*Real.log ((Fintype.card R : ℝ)/p) ∧
    (∑ j : Fin l.length, ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
      (commonMap A (chainLeft μ x₀ l F (j+1) r z)*C*
        (commonMap B (chainRight μ y₀ l H j r z)-commonMap B (chainRight μ y₀ l H (j+1) r z))ᵀ))) ≤
      p*Real.log ((Fintype.card R : ℝ)/p) := by
  let ρ := pi (fun _ : I => μ)
  let A := chainLeftFamily μ x₀ l F
  let B := chainRightFamily μ y₀ l H
  let f := chainLeft μ x₀ l F
  let h := chainRight μ y₀ l H
  have hfpos : ∀ j r z, (f j r z).PosSemidef :=
    fun j r => lefts_posSemidef μ x₀ _ _ (hF r)
  have hf1 : ∀ j r z, f j r z ≤ 1 := fun j r => lefts_le μ x₀ _ _ (hF1 r)
  have hhpos : ∀ j r z, (h j r z).PosSemidef :=
    fun j r => rights_posSemidef μ y₀ _ _ (hH r)
  have hh1 : ∀ j r z, h j r z ≤ 1 := fun j r => rights_le μ y₀ _ _ (hH1 r)
  have hA : ∀ t, (A t).PosSemidef := fun t => hfpos _ _ _
  have hA1 : ∀ t, A t ≤ 1 := fun t => hf1 _ _ _
  have hB : ∀ t, (B t).PosSemidef := fun t => hhpos _ _ _
  have hB1 : ∀ t, B t ≤ 1 := fun t => hh1 _ _ _
  have hfRange : ∀ j, j ≤ l.length → ∀ r z, f j r z ∈ Set.range A := by
    intro j hj r z
    exact ⟨(⟨j, by omega⟩, r, z), rfl⟩
  have hhRange : ∀ j, j ≤ l.length → ∀ r z, h j r z ∈ Set.range B := by
    intro j hj r z
    exact ⟨(⟨j, by omega⟩, r, z), rfl⟩
  let U : ℕ → ℝ := fun j => ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f j r z)) (h j r z))
  let Z : ℕ → ℝ := fun j => ∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (effectEntropy (h j r z)))
  have hmass (j : ℕ) : (∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (h j r z))) = p :=
    (chain_mass μ x₀ y₀ l hN C F H hFlocal hHlocal θ hθL hθR j).trans hm
  have hU (j : ℕ) : -p*Real.log ((Fintype.card R : ℝ)/p) ≤ U j ∧ U j ≤ 0 :=
    averaged_potential_left_bounds ρ C hC θ hθ hθ1 (f j) (h j)
      (hfpos j) (hf1 j) (hhpos j) (hh1 j) hp (hmass j)
  have hZ (j : ℕ) : -p*Real.log ((Fintype.card R : ℝ)/p) ≤ Z j ∧ Z j ≤ 0 :=
    averaged_potential_right_bounds ρ C hC θ hθ hθ1 (f j) (h j)
      (hfpos j) (hf1 j) (hhpos j) (hh1 j) hp (hmass j)
  constructor
  · apply fin_telescope_bound U _ (p*Real.log ((Fintype.card R : ℝ)/p)) _ (by simpa only [neg_mul] using (hU 0).1) (hU _).2
    intro j
    have hs (r : R) := step_left μ x₀ y₀ l[j.val] C A B hA hA1 hB
      (f (j+1) r) (h j r) (hfRange _ (by omega) r)
      (by rw [← chainLeft_step μ x₀ l F j j.isLt]; exact hfRange _ (by omega) r)
      (hhRange _ (by omega) r)
      (chainLeft_next_local μ x₀ l hN F hFlocal j j.isLt r)
      (chainRight_prev_local μ y₀ l hN H hHlocal j j.isLt r)
      (θ r) (hθ r) (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt))
    change _ ≤ (∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f (j+1) r z)) (h (j+1) r z))) -
      ∑ r, ρ.avg (fun z => θ r z*prob C (effectEntropy (f j r z)) (h j r z))
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    have heL : μ.left x₀ l[j.val] (f (j+1) r) = f j r :=
      (chainLeft_step μ x₀ l F j j.isLt r).symm
    have heR : μ.right y₀ l[j.val] (h j r) = h (j+1) r :=
      (chainRight_step μ y₀ l H j j.isLt r).symm
    have hh := hs r
    rw [heL, heR] at hh
    exact hh
  · apply fin_telescope_bound_rev Z _ (p*Real.log ((Fintype.card R : ℝ)/p)) _ (hZ 0).2 (by simpa only [neg_mul] using (hZ _).1)
    intro j
    have hs (r : R) := step_right μ x₀ y₀ l[j.val] C A B hA hB hB1
      (f (j+1) r) (h j r) (hfRange _ (by omega) r) (hhRange _ (by omega) r)
      (by rw [← chainRight_step μ y₀ l H j j.isLt]; exact hhRange _ (by omega) r)
      (chainLeft_next_local μ x₀ l hN F hFlocal j j.isLt r)
      (chainRight_prev_local μ y₀ l hN H hHlocal j j.isLt r)
      (θ r) (hθ r) (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt))
    change _ ≤ (∑ r, ρ.avg (fun z => θ r z*prob C (f j r z) (effectEntropy (h j r z)))) -
      ∑ r, ρ.avg (fun z => θ r z*prob C (f (j+1) r z) (effectEntropy (h (j+1) r z)))
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    have heL : μ.left x₀ l[j.val] (f (j+1) r) = f j r :=
      (chainLeft_step μ x₀ l F j j.isLt r).symm
    have heR : μ.right y₀ l[j.val] (h j r) = h (j+1) r :=
      (chainRight_step μ y₀ l H j j.isLt r).symm
    have hh := hs r
    rw [heL, heR] at hh
    exact hh
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

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law


theorem solution.{u_I,u_X,u_Y,u_R,u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.MixedExposure.chain_error_bounds.{u_I,u_X,u_Y,u_R,u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.MixedExposure.chain_error_bounds.{u_I,u_X,u_Y,u_R,u_m,u_n}
