-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.normalized_error_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:18:32.289159+00:00
-- url     : https://prove2.me/submissions/1078bde0-620a-4cbf-9b5d-b46615222e4d

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/ExposureErrors.lean:L119-L142
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.normalized_error_bounds. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_FiniteProbability_Law_kl_tilt_le
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_chain_fixed_mass
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_massAt_right
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_massAt_left
import Theorems.Thm_OAI_ThresholdParallelRepetition_MixedExposure_chain_error_bounds
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_unitize_distance
import Theorems.Thm_OAI_ThresholdParallelRepetition_ScalarEntropy_negMulLog_subprob

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

lemma hsSq_eq_trace (M : Matrix m n ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, hsSq]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  simp [Complex.mul_re, Complex.normSq_apply]

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

end ThresholdParallelRepetition.QuantumSampling

end
end
end
end
end

end OAI

-- ---- from OAI.Probability.EntangledGames.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

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
lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
lemma point_avg [DecidableEq α] (x : α) (f : α → E) : (point x).avg f = f x := by
  simp [point, avg]

lemma bind_avg (p : Law α) (q : α → Law β) (f : β → E) :
    (p.bind q).avg f = p.avg (fun x => (q x).avg f) := by
  simp only [bind, avg, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

lemma map_avg [DecidableEq β] (p : Law α) (f : α → β) (g : β → E) :
    (p.map f).avg g = p.avg (fun x => g (f x)) := by
  simp only [map, bind_avg, point_avg]

lemma normalize_weight [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ x : α) :
    (∑ y, w y)*(normalize w hw a₀).weight x = w x := by
  rw [normalize]
  split_ifs with h
  · have hx : w x = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hw y)).mp h x (Finset.mem_univ x)
    simp [h, hx]
  · simp only
    field_simp

section Pair
variable [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
lemma first_given (p : Law (α×β)) (b₀ : β) (x : α) (y : β) :
    p.first.weight x*(p.givenFirst b₀ x).weight y = p.weight (x,y) :=
  normalize_weight _ _ _ _
omit [DecidableEq β] in
lemma second_given (p : Law (α×β)) (a₀ : α) (x : α) (y : β) :
    p.second.weight y*(p.givenSecond a₀ y).weight x = p.weight (x,y) :=
  normalize_weight _ _ _ _

omit [DecidableEq α] in
lemma disintegrate_first (p : Law (α×β)) (b₀ : β) (f : α×β → E) :
    p.avg f = p.first.avg (fun x => (p.givenFirst b₀ x).avg (fun y => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, first_given]
omit [DecidableEq β] in
lemma disintegrate_second (p : Law (α×β)) (a₀ : α) (f : α×β → E) :
    p.avg f = p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, second_given]
  exact Finset.sum_comm
end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

end Pi

section Information

lemma mul_log_ratio_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : p ≠ 0 → q ≠ 0) : p-q ≤ p*Real.log (p/q) := by
  by_cases hz : p = 0
  · simp [hz, hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm (hs hz))
  have h := Real.log_le_sub_one_of_pos (div_pos hq' hp')
  have h := mul_le_mul_of_nonneg_left h hp
  rw [Real.log_div hq'.ne' hp'.ne'] at h
  rw [Real.log_div hp'.ne' hq'.ne']
  have he : p*(q/p-1) = q-p := by field_simp
  rw [he] at h
  nlinarith

lemma kl_nonneg (p q : Law α) (hs : Supports p q) : 0 ≤ p.kl q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_log_ratio_lower (p.nonneg x) (q.nonneg x) (hs x))
  simpa [kl, avg, Finset.sum_sub_distrib, p.total, q.total] using h

lemma kl_log_sub (p q : Law α) (hs : Supports p q) :
    p.kl q = p.avg (fun x => Real.log (p.weight x)) -
      p.avg (fun x => Real.log (q.weight x)) := by
  simp only [kl, avg, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [Real.log_div h (hs x h), mul_sub]

lemma map_weight_pos [DecidableEq β] (p : Law α) (f : α → β) (x : α)
    (hx : 0 < p.weight x) : 0 < (p.map f).weight (f x) := by
  have h : p.weight x ≤ (p.map f).weight (f x) := by
    change _ ≤ ∑ y, p.weight y*(point (f y)).weight (f x)
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun y _ => mul_nonneg (p.nonneg y) ((point (f y)).nonneg (f x)))
      (Finset.mem_univ x)
    simpa [point] using hh
  exact hx.trans_le h

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
lemma marginal_avg (p : Law (ι → α)) (i : ι) (f : α → E) :
    (p.marginal i).avg f = p.avg (fun z => f (z i)) := map_avg _ _ _

lemma supports_marginal_pi (p : Law (ι → α)) : Supports p (pi p.marginal) := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt (map_weight_pos p (fun z => z i) z
    (lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)))

lemma avg_log_pi (p : Law (ι → α)) (q : ι → Law α) (hs : Supports p (pi q)) :
    p.avg (fun z => Real.log ((pi q).weight z)) =
      ∑ i, (p.marginal i).avg (fun x => Real.log ((q i).weight x)) := by
  simp_rw [marginal_avg]
  rw [← avg_sum]
  simp only [avg, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p.weight z = 0
  · simp [hz]
  have hq := hs z hz
  change (∏ i, (q i).weight (z i)) ≠ 0 at hq
  rw [pi, Real.log_prod (Finset.prod_ne_zero_iff.mp hq)]

lemma supports_marginal (p : Law (ι → α)) (q : ι → Law α)
    (hs : Supports p (pi q)) (i : ι) : Supports (p.marginal i) (q i) := by
  intro x hx
  by_contra hqx
  apply hx
  change (∑ z, p.weight z*(point (z i)).weight x) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : p.weight z = 0
  · simp [hz]
  have hne := Finset.prod_ne_zero_iff.mp (hs z hz) i (Finset.mem_univ i)
  have hzi : z i ≠ x := by intro he; rw [he, hqx] at hne; exact hne rfl
  simp [point, Ne.symm hzi]

lemma kl_tensorization (p : Law (ι → α)) (q : ι → Law α)
    (hs : Supports p (pi q)) :
    (∑ i, (p.marginal i).kl (q i)) ≤ p.kl (pi q) := by
  have h := kl_nonneg p (pi p.marginal) (supports_marginal_pi p)
  rw [kl_log_sub p _ (supports_marginal_pi p), avg_log_pi p _
    (supports_marginal_pi p)] at h
  rw [kl_log_sub p _ hs, avg_log_pi p _ hs]
  simp_rw [kl_log_sub _ _ (supports_marginal p q hs _)]
  rw [Finset.sum_sub_distrib]
  linarith

omit [DecidableEq α] in
lemma tilt_avg (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    (g : α → ℝ) : (p.tilt f hf ht).avg g = p.avg (fun x => f x*g x) := by
  simp only [avg, tilt, smul_eq_mul, mul_assoc]

omit [DecidableEq α] in
lemma tilt_supports (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    Supports (p.tilt f hf ht) p := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).1

omit [DecidableEq α] in
lemma kl_tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    (p.tilt f hf ht).kl p = p.avg (fun x => f x*Real.log (f x)) := by
  simp only [kl, avg, tilt, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [mul_div_cancel_left₀ _ h, mul_assoc]

lemma avg_indicator (p : Law α) (x : α) :
    p.avg (fun y => if y=x then (1 : ℝ) else 0) = p.weight x := by
  simp [avg]

omit [DecidableEq α] in
lemma coordDensity_eq (q : ι → Law α) (f : (ι → α) → ℝ) (i : ι) (x : α) :
    coordDensity q f i x = (pi (fun j : {j // j ≠ i} => q j)).avg
      (fun r => f ((Equiv.funSplitAt i α).symm (x,r))) := by
  rw [coordDensity, pi_avg_split _ i]
  simp only [update_split, avg_const]

lemma marginal_density_avg (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) (g : α → ℝ) :
    (((pi q).tilt f hf ht).marginal i).avg g =
      (q i).avg (fun x => coordDensity q f i x*g x) := by
  rw [marginal_avg, tilt_avg, pi_avg_split _ i]
  congr 1
  funext x
  rw [coordDensity_eq]
  simp only [Equiv.funSplitAt_symm_apply, dite_eq_left]
  simp only [avg, smul_eq_mul, ← mul_assoc, Finset.sum_mul]

lemma marginal_density_weight (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) (x : α) :
    (((pi q).tilt f hf ht).marginal i).weight x = (q i).weight x*coordDensity q f i x := by
  have h := marginal_density_avg q f hf ht i (fun y => if y=x then (1 : ℝ) else 0)
  rw [avg_indicator] at h
  simpa [avg] using h

lemma marginal_tilt_eq (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) :
    ((pi q).tilt f hf ht).marginal i = (q i).tilt (coordDensity q f i)
      (coordDensity_nonneg q f hf i) (coordDensity_total q f ht i) := by
  cases he : ((pi q).tilt f hf ht).marginal i
  congr 1
  funext x
  exact (congrArg (fun p : Law α => p.weight x) he).symm.trans
    (marginal_density_weight q f hf ht i x)

lemma coord_entropy_sum_le (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) :
    (∑ i, (q i).avg (fun x => coordDensity q f i x*Real.log (coordDensity q f i x))) ≤
      (pi q).avg (fun z => f z*Real.log (f z)) := by
  have h := kl_tensorization ((pi q).tilt f hf ht) q (tilt_supports _ _ _ _)
  simp_rw [marginal_tilt_eq q f hf ht, kl_tilt] at h
  exact h

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

lemma hellinger_le_entropy {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t-1)^2 ≤ t*Real.log t-t+1 := by
  have hs := Real.sqrt_nonneg t
  have hsq := Real.sq_sqrt ht
  by_cases hz : t = 0
  · simp [hz]
  have hp : 0 < Real.sqrt t := Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz))
  have h := Real.self_sub_one_le_mul_log (le_of_lt hp)
  have hl : Real.log t = 2*Real.log (Real.sqrt t) := by
    have he : t = (Real.sqrt t)^2 := hsq.symm
    rw [he, Real.log_pow]
    norm_num
  rw [hl]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr h)]

open FiniteProbability
variable {α : Type u_α} {β : Type u_β} [Fintype α] [Fintype β]

lemma avg_entropy_jensen (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    p.avg f * Real.log (p.avg f) ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := negMulLog_subprob p.weight f p.nonneg p.total.le hf
  change -(∑ x, p.weight x*f x)*Real.log (∑ x, p.weight x*f x) ≥ _ at h
  have he : (∑ x, p.weight x*Real.negMulLog (f x)) =
      -(p.avg (fun x => f x*Real.log (f x))) := by
    simp only [Real.negMulLog_def, Law.avg, smul_eq_mul, mul_neg, ← mul_assoc, neg_mul,
      Finset.sum_neg_distrib]
  rw [he] at h
  change p.avg f*Real.log (p.avg f) ≤ _
  dsimp only [Law.avg, smul_eq_mul] at *
  linarith

lemma avg_hellinger_le_entropy (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ht : p.avg f = 1) :
    p.avg (fun x => (Real.sqrt (f x)-1)^2) ≤ p.avg (fun x => f x*Real.log (f x)) := by
  have h := p.avg_mono fun x => hellinger_le_entropy (hf x)
  have he : p.avg (fun x => f x*Real.log (f x)-f x+1) =
      p.avg (fun x => f x*Real.log (f x)) := by
    simp only [Law.avg, smul_eq_mul, mul_add, mul_sub, mul_one,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, p.total]
    change _ - p.avg f + 1 = _
    rw [ht]; ring
  exact h.trans_eq he

lemma first_density_entropy_le [DecidableEq β] (p : Law (α×β)) (b₀ : β)
    (f : α×β → ℝ) (hf : ∀ z, 0 ≤ f z) :
    p.first.avg (fun x => (p.givenFirst b₀ x).avg (fun y => f (x,y)) *
      Real.log ((p.givenFirst b₀ x).avg (fun y => f (x,y)))) ≤
      p.avg (fun z => f z*Real.log (f z)) := by
  rw [Law.disintegrate_first p b₀]
  exact p.first.avg_mono fun x => avg_entropy_jensen _ _ (fun y => hf (x,y))

lemma second_density_entropy_le [DecidableEq α] (p : Law (α×β)) (a₀ : α)
    (f : α×β → ℝ) (hf : ∀ z, 0 ≤ f z) :
    p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y)) *
      Real.log ((p.givenSecond a₀ y).avg (fun x => f (x,y)))) ≤
      p.avg (fun z => f z*Real.log (f z)) := by
  rw [Law.disintegrate_second p a₀]
  exact p.second.avg_mono fun y => avg_entropy_jensen _ _ (fun x => hf (x,y))

end ScalarEntropy
namespace OperatorEntropy
open Resolvent QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

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

variable [DecidableEq m]
variable {A : Type u_A} {B : Type u_B} [Fintype A] [Fintype B] [DecidableEq n]
end Blocks

section Normalization
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]
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
end Stack

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

omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] [DecidableEq I] [DecidableEq m] [DecidableEq n] in
lemma eventDensity_nonneg (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z)
    {p : ℝ} (hp : 0 < p) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hH : ∀ r z, (H r z).PosSemidef) (z : Profile I X Y) :
    0 ≤ eventDensity θ p C F H z :=
  mul_nonneg (div_nonneg zero_le_one hp.le)
    (Finset.sum_nonneg (fun r _ => mul_nonneg (hθ r z) (prob_nonneg (hF r z) (hH r z))))

omit [DecidableEq X] [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma eventDensity_total (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    {p : ℝ} (hp : 0 < p) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    (pi (fun _ : I => μ)).avg (eventDensity θ p C F H) = 1 := by
  change (pi (fun _ : I => μ)).avg (fun z => (1/p) • ∑ r, θ r z*prob C (F r z) (H r z)) = 1
  rw [avg_smul, avg_sum, hm, smul_eq_mul, one_div, inv_mul_cancel₀ hp.ne']
end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
open FiniteProbability Law ScalarEntropy
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_triangle (C D E : Matrix m n ℂ) : hsSq (C-E) ≤ 2*(hsSq (C-D)+hsSq (D-E)) := by
  have h := hsSq_add_le (C-D) (D-E)
  simpa only [sub_add_sub_cancel] using h

omit [DecidableEq m] [DecidableEq n] in
lemma avg_unitize_triangle {Z : Type u_Z} [Fintype Z] (μ : Law Z)
    (C D : Z → Matrix m n ℂ) (E : Matrix m n ℂ) :
    μ.avg (fun z => hsSq (C z-unitize (D z) E)) ≤
      2*(μ.avg (fun z => hsSq (C z-D z))+μ.avg (fun z => hsSq (D z-unitize (D z) E))) := by
  have h := μ.avg_mono (fun z => hsSq_triangle (C z) (D z) (unitize (D z) E))
  apply h.trans_eq
  change μ.avg (fun z => (2:ℝ) • (hsSq (C z-D z)+hsSq (D z-unitize (D z) E))) = _
  rw [avg_smul, avg_add]
  rfl

variable {X : Type u_X} {Y : Type u_Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
omit [DecidableEq m] [DecidableEq n] [DecidableEq X] in
lemma first_unitize_cost (μ : Law (X×Y)) (y₀ : Y) (f : X×Y → ℝ)
    (hf : ∀ z, 0 ≤ f z) (ht : μ.avg f = 1) (M : X → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = (μ.givenFirst y₀ x).avg (fun y => f (x,y)))
    (E : Matrix m n ℂ) (hE : hsSq E = 1) :
    μ.avg (fun z => hsSq (M z.1-unitize (M z.1) E)) ≤ μ.avg (fun z => f z*Real.log (f z)) := by
  rw [disintegrate_first μ y₀]
  simp only [avg_const, unitize_distance _ _ hE, hM]
  have hmean : μ.first.avg (fun x => (μ.givenFirst y₀ x).avg (fun y => f (x,y))) = 1 := by
    rw [← disintegrate_first]; exact ht
  exact (avg_hellinger_le_entropy μ.first _ (fun x => (μ.givenFirst y₀ x).avg_nonneg (fun y => hf (x,y))) hmean).trans
    (first_density_entropy_le μ y₀ f hf)

omit [DecidableEq m] [DecidableEq n] [DecidableEq Y] in
lemma second_unitize_cost (μ : Law (X×Y)) (x₀ : X) (f : X×Y → ℝ)
    (hf : ∀ z, 0 ≤ f z) (ht : μ.avg f = 1) (N : Y → Matrix m n ℂ)
    (hN : ∀ y, hsSq (N y) = (μ.givenSecond x₀ y).avg (fun x => f (x,y)))
    (E : Matrix m n ℂ) (hE : hsSq E = 1) :
    μ.avg (fun z => hsSq (N z.2-unitize (N z.2) E)) ≤ μ.avg (fun z => f z*Real.log (f z)) := by
  rw [disintegrate_second μ x₀]
  simp only [avg_const, unitize_distance _ _ hE, hN]
  have hmean : μ.second.avg (fun y => (μ.givenSecond x₀ y).avg (fun x => f (x,y))) = 1 := by
    rw [← disintegrate_second]; exact ht
  exact (avg_hellinger_le_entropy μ.second _ (fun y => (μ.givenSecond x₀ y).avg_nonneg (fun x => hf (x,y))) hmean).trans
    (second_density_entropy_le μ x₀ f hf)
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

omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_nonneg : ∀ z, 0 ≤ S.density z := eventDensity_nonneg S.θ S.hθ S.hp S.C S.F S.H S.hF S.hH
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_total : (pi (fun _ : I => S.μ)).avg S.density = 1 :=
  eventDensity_total S.μ S.θ S.hp S.C S.F S.H S.mass
omit [DecidableEq X] [DecidableEq Y] [DecidableEq R] [Nonempty X] [Nonempty Y] [Nonempty R] in
lemma density_le (z : Profile I X Y) : S.density z ≤ 1/S.p := by
  exact (mul_le_mul_of_nonneg_left (S.event_le_one z) (div_nonneg zero_le_one S.hp.le)).trans_eq (mul_one _)

end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- inlined from the rawA_norm solution: its helper lemmas and rawA_norm itself ----
-- (proved here instead of imported: the platform cannot check rawA_norm's published statement)
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

omit [DecidableEq n] [DecidableEq q] in
lemma prob_gram (D : Matrix n q ℂ) (K : Matrix m n ℂ) (L : Matrix p q ℂ) :
    prob D (Kᴴ*K) (Lᴴ*L) = hsSq (K*D*Lᵀ) := by
  simpa only [Matrix.mul_one, prob_one] using prob_pullback D K L (1 : Matrix m m ℂ) (1 : Matrix p p ℂ)
end FilterMass

open Filter Topology
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
end ThresholdParallelRepetition.FiniteProbability.Law
namespace ThresholdParallelRepetition.MixedExposure
open QuantumSampling FiniteProbability Law
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [DecidableEq X] [DecidableEq Y]
variable {m : Type u_m} {n : Type u_n} {u : Type u_u} {v : Type u_v} [Fintype m] [Fintype n] [Fintype u] [Fintype v]
lemma stateAt_norm (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q) = (1/p)*∑ r, (pi (fun _ : I => μ)).avg
      (fun z => θ r z * hsSq (U r (Function.update z i q)*C*(V r (Function.update z i q))ᵀ)) := by
  rw [stateAt, hsSq_weightedBlock _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  ring

variable [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]
omit [DecidableEq m] [DecidableEq n] in
lemma stateAt_norm_gram (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hU : ∀ r z, (U r z)ᴴ*U r z=F r z) (hV : ∀ r z, (V r z)ᴴ*V r z=H r z) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q) = (1/p)*∑ r, (pi (fun _ : I => μ)).avg
      (fun z => θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) := by
  rw [stateAt_norm μ θ hθ hp]
  simp only [← prob_gram, hU, hV]
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

omit [DecidableEq X] [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma massAt_eq_coordDensity (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (i : I)
    (hθL : ∀ r, IgnoresLeft (θ r) i) (hθR : ∀ r, IgnoresRight (θ r) i) (q : X×Y) :
    massAt μ θ p i C F H q = coordDensity (fun _ : I => μ) (eventDensity θ p C F H) i q := by
  unfold massAt coordDensity eventDensity
  simp only [ignores_update (hθL _) (hθR _)]
  rw [show (fun z => (1/p)*∑ r, θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) =
    (fun z => (1/p) • ∑ r, θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) from rfl,
    avg_smul, avg_sum]
  rfl

end ThresholdParallelRepetition.MixedExposure

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
-- [generator] trimmed: open FiniteProbability Law ScalarEntropy
open FiniteProbability Law
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
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
lemma D_norm (j : Fin S.l.length) (q : X×Y) : hsSq (S.D j q) = coordDensity (fun _ : I => S.μ) S.density S.l[j.val] q := by
  rw [D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f (j+1)) (S.h j) q = _
  rw [chain_fixed_mass S.μ S.x₀ S.y₀ S.l S.nodup S.C S.F S.H S.localF S.localH S.θ S.localθL S.localθR]
  exact massAt_eq_coordDensity S.μ S.θ S.p S.C S.F S.H _
    (fun r => S.localθL r _ (List.getElem_mem j.isLt)) (fun r => S.localθR r _ (List.getElem_mem j.isLt)) q

lemma rawA_norm (j : Fin S.l.length) (x : X) : hsSq (S.rawA j x) =
    (S.μ.givenFirst S.y₀ x).avg (fun y => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  rw [rawA, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h (j+1))
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f (j+1)) (S.h (j+1)) (x,S.y₀) = _
  have he : S.h (j+1) = fun r => S.μ.right S.y₀ S.l[j.val] (S.h j r) := by
    funext r; exact chainRight_step S.μ S.y₀ S.l S.H j j.isLt r
  rw [he, massAt_right S.μ S.y₀ S.θ S.p _ S.C _ _
    (chainLeft_next_local S.μ S.x₀ S.l S.nodup S.F S.localF j j.isLt)]
  congr 1; funext y
  rw [← S.D_norm j (x,y), D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  rfl
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- inlined from the rawB_norm solution ----
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

lemma rawB_norm (j : Fin S.l.length) (y : Y) : hsSq (S.rawB j y) =
    (S.μ.givenSecond S.x₀ y).avg (fun x => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] (x,y)) := by
  rw [rawB, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f j) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  change massAt S.μ S.θ S.p S.l[j.val] S.C (S.f j) (S.h j) (S.x₀,y) = _
  have he : S.f j = fun r => S.μ.left S.x₀ S.l[j.val] (S.f (j+1) r) := by
    funext r; exact chainLeft_step S.μ S.x₀ S.l S.F j j.isLt r
  rw [he, massAt_left S.μ S.x₀ S.θ S.p _ S.C _ _
    (chainRight_prev_local S.μ S.y₀ S.l S.nodup S.H S.localH j j.isLt)]
  congr 1; funext x
  rw [← S.D_norm j (x,y), D, stateAt_norm_gram S.μ S.θ S.hθ S.hp _ S.C _ _ (S.f (j+1)) (S.h j)
    (S.U_gram (by omega)) (S.V_gram (by omega))]
  rfl
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI


-- ---- from OAI.Probability.EntangledGames.ExposureErrors ----
namespace OAI

universe u_I u_Z u_X u_Y u_R u_m u_n

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability.Law
variable {I : Type u_I} {Z : Type u_Z} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
omit [DecidableEq Z] in
lemma coord_entropy_nonneg (q : I → Law Z) (f : (I → Z) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : I) :
    0 ≤ (q i).avg (fun z => coordDensity q f i z*Real.log (coordDensity q f i z)) := by
  rw [← kl_tilt (q i) _ (coordDensity_nonneg q f hf i) (coordDensity_total q f ht i)]
  exact kl_nonneg _ _ (tilt_supports _ _ _ _)

lemma list_coord_entropy_sum_le (q : I → Law Z) (f : (I → Z) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (l : List I) (hN : l.Nodup) :
    (∑ j : Fin l.length, (q l[j.val]).avg (fun z => coordDensity q f l[j.val] z*Real.log (coordDensity q f l[j.val] z))) ≤
      (pi q).avg (fun z => f z*Real.log (f z)) := by
  let g : I → ℝ := fun i => (q i).avg (fun z => coordDensity q f i z*Real.log (coordDensity q f i z))
  have hi : Function.Injective (fun j : Fin l.length => l[j.val]) := by
    intro i j h
    apply hN.get_inj_iff.mp
    simpa only [List.get_eq_getElem] using h
  have hs : (∑ j : Fin l.length, g l[j.val]) ≤ ∑ i, g i := by
    rw [← Finset.sum_image (f := g) (s := Finset.univ) (Set.injOn_of_injective hi)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => coord_entropy_nonneg q f hf ht i)
  exact hs.trans (coord_entropy_sum_le q f hf ht)
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

lemma norm_cost_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1))) ≤ Real.log (1/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2))) ≤ Real.log (1/S.p) := by
  have he := list_coord_entropy_sum_le (fun _ : I => S.μ) S.density S.density_nonneg S.density_total S.l S.nodup
  have hlog := kl_tilt_le (pi (fun _ : I => S.μ)) S.density S.density_nonneg S.density_total
    (one_div_pos.mpr S.hp) S.density_le
  rw [kl_tilt] at hlog
  have hb := he.trans hlog
  have hA (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1)) ≤
      S.μ.avg (fun z => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z *
        Real.log (coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z)) := by
    exact first_unitize_cost S.μ S.y₀
      (coordDensity (fun _ : I => S.μ) S.density S.l[j.val])
      (coordDensity_nonneg _ _ S.density_nonneg S.l[j.val])
      (coordDensity_total _ _ S.density_total S.l[j.val]) (S.rawA j) (S.rawA_norm j) E hE
  have hB (j : Fin S.l.length) : S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2)) ≤
      S.μ.avg (fun z => coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z *
        Real.log (coordDensity (fun _ : I => S.μ) S.density S.l[j.val] z)) := by
    exact second_unitize_cost S.μ S.x₀
      (coordDensity (fun _ : I => S.μ) S.density S.l[j.val])
      (coordDensity_nonneg _ _ S.density_nonneg S.l[j.val])
      (coordDensity_total _ _ S.density_total S.l[j.val]) (S.rawB j) (S.rawB_norm j) E hE
  exact ⟨(Finset.sum_le_sum fun j _ => hA j).trans hb, (Finset.sum_le_sum fun j _ => hB j).trans hb⟩

lemma normalized_error_bounds (E : Matrix ((S.J×m)×(R×Profile I X Y)) ((S.J×n)×(R×Profile I X Y)) ℂ)
    (hE : hsSq E = 1) :
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) ∧
    (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤ 4*Real.log ((Fintype.card R : ℝ)/S.p) := by
  have hcard : (1:ℝ) ≤ Fintype.card R := by exact_mod_cast Fintype.card_pos (α := R)
  have hl : Real.log (1/S.p) ≤ Real.log ((Fintype.card R : ℝ)/S.p) :=
    Real.log_le_log (one_div_pos.mpr S.hp) (div_le_div_of_nonneg_right hcard S.hp.le)
  have ha := S.raw_error_bounds
  have hb := S.norm_cost_bounds E hE
  constructor
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      avg_unitize_triangle S.μ (S.D j) (fun q => S.rawA j q.1) E)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    change (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.M j E q.1))) ≤
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawA j q.1)))+
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawA j q.1-S.M j E q.1))) at hh
    linarith
  · have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      avg_unitize_triangle S.μ (S.D j) (fun q => S.rawB j q.2) E)
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    change (∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.N j E q.2))) ≤
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.D j q-S.rawB j q.2)))+
      2*(∑ j : Fin S.l.length, S.μ.avg (fun q => hsSq (S.rawB j q.2-S.N j E q.2))) at hh
    linarith
end EventSystem
end ThresholdParallelRepetition.MixedExposure

end

end OAI

-- ---- platform node ----
open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.MixedExposure OAI.ThresholdParallelRepetition.MixedExposure.EventSystem
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law


theorem solution.{u_I,u_X,u_Y,u_R,u_m,u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.normalized_error_bounds.{u_I,u_X,u_Y,u_R,u_m,u_n} := @_root_.OAI.ThresholdParallelRepetition.MixedExposure.EventSystem.normalized_error_bounds.{u_I,u_X,u_Y,u_R,u_m,u_n}
