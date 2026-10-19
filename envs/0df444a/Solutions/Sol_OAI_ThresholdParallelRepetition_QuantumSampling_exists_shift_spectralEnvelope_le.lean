-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.exists_shift_spectralEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:48:56.703554+00:00
-- url     : https://prove2.me/submissions/731d3998-4109-4395-8c61-f4543f017ba1

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/SpectralBins.lean:L377-L399
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.exists_shift_spectralEnvelope_le. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_cfc_eq
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_spectral_mixed

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

lemma floor_shift_monotone (u : ℝ) : Monotone (fun s : ℝ => (⌊u+s⌋ : ℝ)) := by
  intro s t h
  change (⌊u+s⌋ : ℝ) ≤ (⌊u+t⌋ : ℝ)
  exact_mod_cast Int.floor_mono (show u+s ≤ u+t by linarith)

lemma integral_floor_shift (u : ℝ) : (∫ s in (0:ℝ)..1, (⌊u+s⌋ : ℝ)) = u := by
  let c := 1 - Int.fract u
  have hc0 : 0 ≤ c := by dsimp [c]; linarith [Int.fract_lt_one u]
  have hc1 : c ≤ 1 := by dsimp [c]; linarith [Int.fract_nonneg u]
  have hu : Int.fract u + (⌊u⌋ : ℝ) = u := Int.fract_add_floor u
  have hleft : (∫ s in (0:ℝ)..c, (⌊u+s⌋ : ℝ)) = c * (⌊u⌋ : ℝ) := by
    calc
      _ = ∫ _ in (0:ℝ)..c, (⌊u⌋ : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc0
        intro s hs
        dsimp only
        have he : ⌊u+s⌋ = ⌊u⌋ := Int.floor_eq_iff.mpr ⟨by linarith [Int.fract_nonneg u, hs.1], by dsimp [c] at hs; linarith [hs.2]⟩
        rw [he]
      _ = _ := by simp
  have hright : (∫ s in c..(1:ℝ), (⌊u+s⌋ : ℝ)) = (1-c) * ((⌊u⌋ : ℝ)+1) := by
    calc
      _ = ∫ _ in c..(1:ℝ), ((⌊u⌋ : ℝ)+1) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hc1
        intro s hs
        dsimp only
        have he : ⌊u+s⌋ = ⌊u⌋ + 1 := Int.floor_eq_iff.mpr ⟨by push_cast; dsimp [c] at hs; linarith [hs.1], by push_cast; linarith [Int.fract_lt_one u, hs.2]⟩
        rw [he]; push_cast; rfl
      _ = _ := by simp; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((floor_shift_monotone u).intervalIntegrable (μ := volume) (a := 0) (b := c))
    ((floor_shift_monotone u).intervalIntegrable (μ := volume) (a := c) (b := 1)), hleft, hright]
  dsimp [c]
  nlinarith

lemma separated_nonneg (u v s : ℝ) : 0 ≤ separated u v s := by unfold separated; split <;> norm_num
lemma separated_le_one (u v s : ℝ) : separated u v s ≤ 1 := by unfold separated; split <;> norm_num
lemma separated_symm (u v s : ℝ) : separated u v s = separated v u s := by simp [separated, eq_comm]

lemma separated_measurable (u v : ℝ) : Measurable (separated u v) := by
  unfold separated
  exact measurable_const.ite (measurableSet_eq_fun ((measurable_const.add measurable_id).floor)
    ((measurable_const.add measurable_id).floor)) measurable_const

lemma separated_integrable (u v a b : ℝ) : IntervalIntegrable (separated u v) volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun' (separated_measurable u v).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by dsimp only; rw [Real.norm_eq_abs, abs_of_nonneg (separated_nonneg u v s)]; exact separated_le_one u v s

lemma separated_le_floor_sub {u v : ℝ} (huv : u ≤ v) (s : ℝ) :
    separated u v s ≤ (⌊v+s⌋ : ℝ) - (⌊u+s⌋ : ℝ) := by
  unfold separated
  split_ifs with h
  · rw [h]; simp
  · have hle : ⌊u+s⌋ ≤ ⌊v+s⌋ := Int.floor_mono (by linarith)
    have hlt : ⌊u+s⌋ + 1 ≤ ⌊v+s⌋ := by omega
    exact_mod_cast (show (1:ℤ) ≤ ⌊v+s⌋ - ⌊u+s⌋ by omega)

lemma integral_separated_le {u v : ℝ} :
    (∫ s in (0:ℝ)..1, separated u v s) ≤ |u-v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [show separated u v = separated v u by funext s; exact separated_symm _ _ _]
    simpa only [abs_sub_comm] using this (le_of_not_ge huv)
  calc
    _ ≤ ∫ s in (0:ℝ)..1, ((⌊v+s⌋ : ℝ) - (⌊u+s⌋ : ℝ)) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (separated_integrable _ _ _ _)
        (((floor_shift_monotone v).intervalIntegrable).sub ((floor_shift_monotone u).intervalIntegrable))
      intro s _
      exact separated_le_floor_sub huv s
    _ = v-u := by rw [intervalIntegral.integral_sub
      ((floor_shift_monotone v).intervalIntegrable) ((floor_shift_monotone u).intervalIntegrable),
      integral_floor_shift, integral_floor_shift]
    _ = |u-v| := by rw [abs_of_nonpos (by linarith)]; ring

lemma binEnvelope_integrable (a b ε l r : ℝ) :
    IntervalIntegrable (binEnvelope a b ε) volume l r := by
  exact intervalIntegrable_const.add ((separated_integrable _ _ _ _).const_mul _)

lemma log_difference_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * (Real.log b - Real.log a) ≤ b-a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  calc
    _ ≤ a*(b/a-1) := hh
    _ = b-a := by field_simp

lemma logarithmic_envelope_bound {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (a-b)^2 + 2*a*b*(|Real.log a-Real.log b|/ε) ≤ 3/ε * |a-b| * (a+b) := by
  wlog hab : a ≤ b generalizing a b
  · have hh := this hb ha (le_of_not_ge hab)
    simpa only [abs_sub_comm b a, abs_sub_comm (Real.log b) (Real.log a),
      add_comm b a, sub_sq_comm b a, mul_right_comm (2:ℝ) b a] using hh
  rw [abs_of_nonpos (sub_nonpos.mpr hab)]
  by_cases ha0 : a = 0
  · subst a
    simp only [zero_sub, neg_neg, zero_mul, mul_zero, zero_add, neg_sq, add_zero]
    apply (le_mul_of_one_le_left (sq_nonneg b) (show 1 ≤ 3/ε by apply (le_div_iff₀ hε).mpr; linarith)).trans_eq
    ring
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_lt_of_le hap hab
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hap hab))]
  have hl := log_difference_bound hap hab
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*b by positivity)
  have hsq : (a-b)^2 ≤ (b-a)*(a+b) := by nlinarith
  apply (mul_le_mul_iff_of_pos_right hε).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hε1 (sq_nonneg (a-b)), mul_nonneg ha (sub_nonneg.mpr hab)]

lemma integral_binEnvelope_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s in (0:ℝ)..1, binEnvelope a b ε s) ≤ 3/ε * |a-b| * (a+b) := by
  calc
    _ ≤ (a-b)^2 + 2*a*b*(|Real.log a-Real.log b|/ε) := by
      unfold binEnvelope
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((separated_integrable _ _ _ _).const_mul _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [sub_zero, one_smul]
      apply add_le_add_right
      have hi := integral_separated_le (u := Real.log a/ε) (v := Real.log b/ε)
      rw [← sub_div, abs_div, abs_of_pos hε] at hi
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := logarithmic_envelope_bound ha hb hε hε1

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma unitary_row_normSq {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) (i : n) :
    ∑ j, Complex.normSq (U i j) = 1 := by
  have h := congrArg Complex.re (congrFun (congrFun hU i) i)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.re_sum, Complex.one_re, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] using h

lemma unitary_col_normSq {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (j : n) :
    ∑ i, Complex.normSq (U i j) = 1 := by
  simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj] using
    unitary_row_normSq (U := Uᴴ) (by simpa only [Matrix.conjTranspose_conjTranspose] using hU) j

lemma hsSq_eq_sum_eigenvalues_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hsSq A = ∑ i, (hA.eigenvalues i)^2 := by
  have h := hsSq_cfc_eq hA (fun t => t)
  erw [cfc_id' ℝ A hA] at h
  exact h

lemma overlap_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ overlap hA hB i j := Complex.normSq_nonneg _

lemma overlap_row {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i : n) :
    ∑ j, overlap hA hB i j = 1 := by
  apply unitary_row_normSq
  have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hA.eigenvectorUnitary = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  have h2 : (hB.eigenvectorUnitary : Matrix n n ℂ) * (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hB.eigenvectorUnitary : Matrix n n ℂ), h2, Matrix.one_mul, h1]

lemma overlap_col {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (j : n) :
    ∑ i, overlap hA hB i j = 1 := by
  apply unitary_col_normSq
  have h1 : (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.property
  have h2 : (hB.eigenvectorUnitary : Matrix n n ℂ)ᴴ * hB.eigenvectorUnitary = 1 :=
    Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hA.eigenvectorUnitary : Matrix n n ℂ), h1, Matrix.one_mul, h2]

lemma overlap_distance {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, (hA.eigenvalues i - hB.eigenvalues j)^2 * overlap hA hB i j) = hsSq (A-B) := by
  have h := hsSq_spectral_mixed hA hB (fun t => t) (fun t => t)
  erw [cfc_id' ℝ A hA, cfc_id' ℝ B hB] at h
  exact h.symm

lemma overlap_square_sum_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, (hA.eigenvalues i + hB.eigenvalues j)^2 * overlap hA hB i j) ≤
    2 * (hsSq A + hsSq B) := by
  calc
    _ ≤ ∑ i, ∑ j, (2*(hA.eigenvalues i)^2 + 2*(hB.eigenvalues j)^2) * overlap hA hB i j := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (hA.eigenvalues i-hB.eigenvalues j)]) (overlap_nonneg _ _ _ _)
    _ = _ := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => 2*(hB.eigenvalues j)^2 * overlap hA hB i j)]
      simp_rw [← Finset.mul_sum, overlap_row, overlap_col, mul_one]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← hsSq_eq_sum_eigenvalues_sq hA,
        ← hsSq_eq_sum_eigenvalues_sq hB]
      ring

lemma overlap_transport_le {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∑ i, ∑ j, |hA.eigenvalues i - hB.eigenvalues j| *
      (hA.eigenvalues i + hB.eigenvalues j) * overlap hA hB i j) ≤
      Real.sqrt (hsSq (A-B)) * Real.sqrt (2 * (hsSq A + hsSq B)) := by
  let r : n × n → ℝ := fun ij => |hA.eigenvalues ij.1 - hB.eigenvalues ij.2| *
    (hA.eigenvalues ij.1 + hB.eigenvalues ij.2) * overlap hA hB ij.1 ij.2
  let f : n × n → ℝ := fun ij => (hA.eigenvalues ij.1 - hB.eigenvalues ij.2)^2 * overlap hA hB ij.1 ij.2
  let g : n × n → ℝ := fun ij => (hA.eigenvalues ij.1 + hB.eigenvalues ij.2)^2 * overlap hA hB ij.1 ij.2
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (n × n))
    (r := r) (f := f) (g := g)
    (fun ij _ => mul_nonneg (sq_nonneg _) (overlap_nonneg _ _ _ _))
    (fun ij _ => mul_nonneg (sq_nonneg _) (overlap_nonneg _ _ _ _))
    (fun ij _ => by dsimp [r,f,g]; rw [mul_pow, mul_pow, sq_abs]; exact le_of_eq (by ring))
  have hf : ∑ ij, f ij = hsSq (A-B) := by rw [Fintype.sum_prod_type]; exact overlap_distance hA hB
  have hg : ∑ ij, g ij ≤ 2 * (hsSq A + hsSq B) := by rw [Fintype.sum_prod_type]; exact overlap_square_sum_le hA hB
  rw [hf] at hc
  have hbound := hc.trans (mul_le_mul_of_nonneg_left hg (hsSq_nonneg _))
  have hr : ∑ ij, r ij = ∑ i, ∑ j, |hA.eigenvalues i - hB.eigenvalues j| *
      (hA.eigenvalues i + hB.eigenvalues j) * overlap hA hB i j := by rw [Fintype.sum_prod_type]
  rw [hr] at hbound
  have hprod : (Real.sqrt (hsSq (A-B)) * Real.sqrt (2*(hsSq A+hsSq B)))^2 =
      hsSq (A-B)*(2*(hsSq A+hsSq B)) := by
    rw [mul_pow, Real.sq_sqrt (hsSq_nonneg _), Real.sq_sqrt (by linarith [hsSq_nonneg A, hsSq_nonneg B])]
  have hnon : 0 ≤ Real.sqrt (hsSq (A-B)) * Real.sqrt (2*(hsSq A+hsSq B)) := by positivity
  rw [← hprod] at hbound
  exact le_of_sq_le_sq hbound hnon

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma spectralEnvelope_integrable {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ε : ℝ) : IntervalIntegrable (spectralEnvelope hA hB ε) volume 0 1 := by
  unfold spectralEnvelope
  simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
    (fun i _ => IntervalIntegrable.sum Finset.univ
      (fun j _ => (binEnvelope_integrable (hA.eigenvalues i) (hB.eigenvalues j) ε 0 1).mul_const (overlap hA hB i j)))

lemma integral_spectralEnvelope_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s in (0:ℝ)..1, spectralEnvelope hA.isHermitian hB.isHermitian ε s) ≤
    3/ε * (Real.sqrt (hsSq (A-B)) * Real.sqrt (2*(hsSq A+hsSq B))) := by
  unfold spectralEnvelope
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (by simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun j _ => (binEnvelope_integrable (hA.isHermitian.eigenvalues i) (hB.isHermitian.eigenvalues j) ε 0 1).mul_const (overlap hA.isHermitian hB.isHermitian i j))))]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (binEnvelope_integrable _ _ _ _ _).mul_const _),
    intervalIntegral.integral_mul_const]
  calc
    _ ≤ ∑ i, ∑ j, (3/ε * |hA.isHermitian.eigenvalues i-hB.isHermitian.eigenvalues j| *
        (hA.isHermitian.eigenvalues i+hB.isHermitian.eigenvalues j)) * overlap hA.isHermitian hB.isHermitian i j := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_right
        (integral_binEnvelope_le (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j) hε hε1)
        (overlap_nonneg _ _ _ _)
    _ = (3/ε) * (∑ i, ∑ j, |hA.isHermitian.eigenvalues i-hB.isHermitian.eigenvalues j| *
        (hA.isHermitian.eigenvalues i+hB.isHermitian.eigenvalues j) * overlap hA.isHermitian hB.isHermitian i j) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (overlap_transport_le hA.isHermitian hB.isHermitian) (by positivity)

lemma integral_spectralEnvelope_unit_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAe : hsSq A = 1) (hBe : hsSq B = 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ s in (0:ℝ)..1, spectralEnvelope hA.isHermitian hB.isHermitian ε s) ≤
    (6/ε) * Real.sqrt (hsSq (A-B)) := by
  have h := integral_spectralEnvelope_le hA hB hε hε1
  rw [hAe, hBe] at h
  norm_num at h
  convert h using 1; ring

lemma weighted_sqrt_le {ι : Type u_ι} [Fintype ι] (w e : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hE : ∀ i, 0 ≤ e i) (hs : ∑ i, w i = 1) :
    (∑ i, w i * Real.sqrt (e i)) ≤ Real.sqrt (∑ i, w i * e i) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => w i * Real.sqrt (e i)) (f := fun i => w i) (g := fun i => w i * e i)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (hE i))
    (fun i _ => by rw [mul_pow, Real.sq_sqrt (hE i)]; exact le_of_eq (by ring))
  rw [hs, one_mul, ← Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hE i)))] at hc
  exact le_of_sq_le_sq hc (Real.sqrt_nonneg _)

lemma exists_shift_spectralEnvelope_le {ι : Type u_ι} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (A B : ι → Matrix n n ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hAe : ∀ i, hsSq (A i) = 1) (hBe : ∀ i, hsSq (B i) = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ s : ℝ, (∑ i, w i * spectralEnvelope (hA i).isHermitian (hB i).isHermitian ε s) ≤
      (6/ε) * Real.sqrt (∑ i, w i * hsSq (A i-B i)) := by
  let F : ℝ → ℝ := fun s => ∑ i, w i * spectralEnvelope (hA i).isHermitian (hB i).isHermitian ε s
  have hF : IntervalIntegrable F volume 0 1 := by
    simpa only [F, Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun i _ => (spectralEnvelope_integrable (hA i).isHermitian (hB i).isHermitian ε).const_mul (w i))
  let : IsProbabilityMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := ⟨by simp⟩
  obtain ⟨s, hsF⟩ := MeasureTheory.exists_le_integral hF.1
  refine ⟨s, hsF.trans ?_⟩
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  unfold F
  rw [intervalIntegral.integral_finsetSum (fun i _ => (spectralEnvelope_integrable _ _ _).const_mul _)]
  simp_rw [intervalIntegral.integral_const_mul]
  calc
    _ ≤ ∑ i, w i * ((6/ε) * Real.sqrt (hsSq (A i-B i))) := by
      apply Finset.sum_le_sum; intro i _
      exact mul_le_mul_of_nonneg_left (integral_spectralEnvelope_unit_le (hA i) (hB i) (hAe i) (hBe i) hε hε1) (hw i)
    _ = (6/ε) * ∑ i, w i * Real.sqrt (hsSq (A i-B i)) := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_sqrt_le w _ hw (fun i => hsSq_nonneg _) hs) (by positivity)

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
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory


theorem solution.{u_n,u_ι} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.exists_shift_spectralEnvelope_le.{u_n,u_ι} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.exists_shift_spectralEnvelope_le.{u_n,u_ι}
