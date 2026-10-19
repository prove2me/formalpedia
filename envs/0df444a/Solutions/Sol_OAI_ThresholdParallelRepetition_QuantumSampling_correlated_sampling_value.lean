-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.correlated_sampling_value
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:03:57.563988+00:00
-- url     : https://prove2.me/submissions/1b0726ca-292e-41fc-a2e8-da2af9d300cc

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CorrelatedSampling.lean:L304-L381
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.correlated_sampling_value. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_binFilter_contraction
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_exists_shift_spectralEnvelope_le
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_filter_mass_bounds
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_finite_filter_value_unnormalized
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_cfc_eq
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_difference_le
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_spectral_mixed
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_polar_crossBins_error_le
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_polar_gram
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_roundedAbs_eq_sum

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

lemma hsSq_cfc_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ)
    (hf : ∀ s t : ℝ, (f s - f t)^2 ≤ L * (s - t)^2) :
    hsSq (cfc f A - cfc f B) ≤ L * hsSq (A - B) := by
  have hident := hsSq_spectral_mixed hA hB (fun x => x) (fun x => x)
  erw [cfc_id' ℝ A hA, cfc_id' ℝ B hB] at hident
  rw [hsSq_spectral_mixed hA hB, hident, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (hf (hA.eigenvalues i) (hB.eigenvalues j)) (Complex.normSq_nonneg _)

lemma hsSq_abs_sub_le [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hsSq (cfc (fun t : ℝ => |t|) A - cfc (fun t : ℝ => |t|) B) ≤ hsSq (A - B) := by
  simpa using hsSq_cfc_sub_le hA hB (fun t : ℝ => |t|) 1 (fun s t => by
    have h := abs_abs_sub_abs_le_abs_sub s t
    nlinarith [sq_nonneg (|s-t| - |(|s| - |t|)|), abs_nonneg (s-t), abs_nonneg (|s|-|t|),
      sq_abs (s-t), sq_abs (|s|-|t|)])

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

lemma block_diagonal_pos [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  have hRa := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hRb := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  have hR : (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B))ᴴ *
      (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B)) = Matrix.fromBlocks A 0 0 B := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hRa, hRb,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  rw [← hR]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [Fintype m] [Fintype n] in
lemma dilation_isHermitian (M : Matrix m n ℂ) : (dilation M).IsHermitian := by
  unfold Matrix.IsHermitian dilation
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_conjTranspose]

lemma abs_square [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun t : ℝ => |t|) A * cfc (fun t : ℝ => |t|) A = A * A := by
  erw [← cfc_mul (fun t : ℝ => |t|) (fun t : ℝ => |t|) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun t : ℝ => t * t) A := by
      apply cfc_congr
      intro t _
      nlinarith [sq_abs t]
    _ = cfc (fun t : ℝ => t) A * cfc (fun t : ℝ => t) A := by
      erw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by erw [cfc_id' ℝ A hA]

lemma abs_eq_sqrt_square [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun t : ℝ => |t|) A = CFC.sqrt (A * A) := by
  apply Eq.symm
  exact CFC.sqrt_unique (abs_square hA) (cfc_nonneg fun t _ => abs_nonneg t)

lemma sqrt_block_diagonal [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  have hpos : 0 ≤ Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) :=
    (block_diagonal_pos (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A))
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg
  apply CFC.sqrt_unique _ hpos
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, CFC.sqrt_mul_sqrt_self _ hA.nonneg, CFC.sqrt_mul_sqrt_self _ hB.nonneg]

lemma abs_dilation [DecidableEq m] [DecidableEq n] (M : Matrix m n ℂ) :
    cfc (fun t : ℝ => |t|) (dilation M) =
      Matrix.fromBlocks (CFC.sqrt (M * Mᴴ)) 0 0 (CFC.sqrt (Mᴴ * M)) := by
  rw [abs_eq_sqrt_square (dilation_isHermitian M)]
  unfold dilation
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  exact sqrt_block_diagonal (Matrix.posSemidef_self_mul_conjTranspose M)
    (Matrix.posSemidef_conjTranspose_mul_self M)

theorem hsSq_right_absolute_sub_le [DecidableEq m] [DecidableEq n] (M N : Matrix m n ℂ) :
    hsSq (CFC.sqrt (Mᴴ * M) - CFC.sqrt (Nᴴ * N)) ≤ 2 * hsSq (M - N) := by
  have h := hsSq_abs_sub_le (dilation_isHermitian M) (dilation_isHermitian N)
  rw [abs_dilation M, abs_dilation N] at h
  simp only [dilation, fromBlocks_sub, sub_self, hsSq_blocks, hsSq_zero, zero_add, add_zero] at h
  rw [← Matrix.conjTranspose_sub, hsSq_conjTranspose] at h
  linarith [hsSq_nonneg (CFC.sqrt (M * Mᴴ) - CFC.sqrt (N * Nᴴ))]

end ThresholdParallelRepetition.QuantumSampling

end

end OAI

-- ---- from OAI.Probability.EntangledGames.SpectralBins ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma separated_nonneg (u v s : ℝ) : 0 ≤ separated u v s := by unfold separated; split <;> norm_num
lemma binEnvelope_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ε s : ℝ) :
    0 ≤ binEnvelope a b ε s := by
  unfold binEnvelope
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (separated_nonneg _ _ _))

lemma binWeight_nonneg (a ε s : ℝ) : 0 ≤ binWeight a ε s := by
  unfold binWeight; split <;> positivity

lemma binWeight_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (s : ℝ) :
    binWeight a ε s ≤ a := by
  unfold binWeight
  split_ifs with hap
  · apply le_trans (b := Real.exp (Real.log a))
    · apply Real.exp_le_exp.mpr
      have hf := Int.floor_le (Real.log a/ε+s)
      have hm := mul_le_mul_of_nonneg_left hf hε.le
      have he : ε*(Real.log a/ε+s) = Real.log a + ε*s := by field_simp
      linarith
    · exact (Real.exp_log hap).le
  · exact ha

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma hsSq_eq_sum_eigenvalues_sq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hsSq A = ∑ i, (hA.eigenvalues i)^2 := by
  have h := hsSq_cfc_eq hA (fun t => t)
  erw [cfc_id' ℝ A hA] at h
  exact h

lemma overlap_nonneg {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : n) :
    0 ≤ overlap hA hB i j := Complex.normSq_nonneg _

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Interval
open Matrix MeasureTheory
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma hsSq_sqrt_gram (M : Matrix n n ℂ) : hsSq (CFC.sqrt (Mᴴ * M)) = hsSq M := by
  have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ*M))).isHermitian.eq
  rw [hsSq_eq_trace, h, CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg,
    ← hsSq_eq_trace]

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

lemma binIndicator_nonneg (ε s : ℝ) (l : ℤ) (a : ℝ) : 0 ≤ binIndicator ε s l a := by
  unfold binIndicator; split <;> norm_num
lemma binIndicator_sq (ε s : ℝ) (l : ℤ) (a : ℝ) : (binIndicator ε s l a)^2 = binIndicator ε s l a := by
  unfold binIndicator; split <;> norm_num
lemma binIndicator_mul_ne (ε s : ℝ) {l k : ℤ} (hlk : l ≠ k) (a : ℝ) :
    binIndicator ε s l a * binIndicator ε s k a = 0 := by
  unfold binIndicator
  split_ifs <;> simp_all

lemma sum_binIndicator_weight_sq_le (L : Finset ℤ) (ε s a : ℝ) :
    (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a)^2) ≤ (binWeight a ε s)^2 := by
  simp only [binIndicator_sq]
  by_cases ha : 0 < a
  · simp only [binIndicator, ha, true_and, mul_ite, mul_one, mul_zero, binWeight, ite_true]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · positivity
  · simp [binIndicator, ha, binWeight]

lemma scalar_mismatch_le (L : Finset ℤ) (ε s : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a-binIndicator ε s l b)^2) ≤
      binEnvelope a b ε s := by
  have hh : (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a-binIndicator ε s l b)^2) ≤ a^2+b^2 := by
    calc
      _ ≤ ∑ l ∈ L, (binScale ε s l)^2 * ((binIndicator ε s l a)^2+(binIndicator ε s l b)^2) := by
        apply Finset.sum_le_sum; intro l _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [mul_nonneg (binIndicator_nonneg ε s l a) (binIndicator_nonneg ε s l b)]
      _ = (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l a)^2) +
        (∑ l ∈ L, (binScale ε s l)^2 * (binIndicator ε s l b)^2) := by simp [mul_add, Finset.sum_add_distrib]
      _ ≤ (binWeight a ε s)^2 + (binWeight b ε s)^2 := add_le_add
          (sum_binIndicator_weight_sq_le L ε s a) (sum_binIndicator_weight_sq_le L ε s b)
      _ ≤ a^2+b^2 := by
        have ha' := binWeight_le ha hε s
        have hb' := binWeight_le hb hε s
        nlinarith [binWeight_nonneg a ε s, binWeight_nonneg b ε s]
  by_cases ha0 : a = 0
  · simpa [binEnvelope, ha0] using hh
  by_cases hb0 : b = 0
  · simpa [binEnvelope, hb0] using hh
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases he : ⌊Real.log a/ε+s⌋ = ⌊Real.log b/ε+s⌋
  · have hi : ∀ l, binIndicator ε s l a = binIndicator ε s l b := by intro l; simp [binIndicator, hap, hbp, he]
    simp only [hi, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    exact binEnvelope_nonneg ha hb ε s
  · have hen : binEnvelope a b ε s = a^2+b^2 := by simp only [binEnvelope, separated, ite_eq_right he]; ring
    rw [hen]; exact hh

variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma binProjection_hermitian (A : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) :
    (binProjection A ε s l).IsHermitian := (cfc_predicate (binIndicator ε s l) A).isHermitian

lemma binProjection_sq {A : Matrix n n ℂ} (_hA : A.IsHermitian) (ε s : ℝ) (l : ℤ) :
    binProjection A ε s l * binProjection A ε s l = binProjection A ε s l := by
  unfold binProjection
  erw [← cfc_mul (binIndicator ε s l) (binIndicator ε s l) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro a _
  simpa only [pow_two] using binIndicator_sq ε s l a

lemma binProjection_orthogonal {A : Matrix n n ℂ} (_hA : A.IsHermitian) (ε s : ℝ)
    {l k : ℤ} (hlk : l ≠ k) : binProjection A ε s l * binProjection A ε s k = 0 := by
  unfold binProjection
  erw [← cfc_mul (binIndicator ε s l) (binIndicator ε s k) A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 0) A := by apply cfc_congr; intro a _; exact binIndicator_mul_ne ε s hlk a
    _ = 0 := cfc_zero ℝ A

lemma binProjection_mismatch_le (L : Finset ℤ) {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    (∑ l ∈ L, (binScale ε s l)^2 * hsSq (binProjection A ε s l-binProjection B ε s l)) ≤
    spectralEnvelope hA.isHermitian hB.isHermitian ε s := by
  unfold binProjection spectralEnvelope
  simp_rw [hsSq_spectral_mixed hA.isHermitian hB.isHermitian, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro j _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (scalar_mismatch_le L ε s (hA.eigenvalues_nonneg i) (hB.eigenvalues_nonneg j) hε)
    (overlap_nonneg _ _ _ _)

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

lemma rightAbs_pos (M : Matrix m n ℂ) : (rightAbs M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
lemma supportInverse_bin {A : Matrix n n ℂ} (hA : A.IsHermitian) (ε s : ℝ) (l : ℤ) :
    (supportInverse A*A)*binProjection A ε s l = binProjection A ε s l := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  unfold supportInverse binProjection
  calc
    _ = cfc (fun t : ℝ => t⁻¹*t*binIndicator ε s l t) A := by
      calc
        _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A * cfc (binIndicator ε s l) A := by rw [hid]
        _ = _ := by
          erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t⁻¹*t) (binIndicator ε s l) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ = _ := by
      apply cfc_congr; intro t _
      by_cases ht : 0 < t
      · simp [ne_of_gt ht]
      · simp [binIndicator, ht]

lemma polar_gram_bin (M : Matrix m n ℂ) (ε s : ℝ) (l : ℤ) :
    ((polar M)ᴴ*polar M)*binProjection (rightAbs M) ε s l = binProjection (rightAbs M) ε s l := by
  rw [polar_gram]
  exact supportInverse_bin (rightAbs_pos M).isHermitian ε s l

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma projection_le_one {P : Matrix n n ℂ} (hP : P.IsHermitian) (hPP : P*P=P) : P ≤ 1 := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (1-P)
  have he : (1-P)ᴴ*(1-P)=1-P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.eq]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP, sub_self, sub_zero]
  rw [he] at h
  exact Matrix.le_iff.mpr h

lemma roundedAbs_energy_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : hsSq (roundedAbs A ε s) ≤ hsSq A := by
  rw [roundedAbs, hsSq_cfc_eq hA.isHermitian, hsSq_eq_sum_eigenvalues_sq hA.isHermitian]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [binWeight_le (hA.eigenvalues_nonneg i) hε s, binWeight_nonneg (hA.isHermitian.eigenvalues i) ε s]

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
lemma hsSq_sum_orthogonal {ι : Type u_ι} [Fintype ι] [DecidableEq ι]
    (F : ι → Matrix m n ℂ) (hF : ∀ i j, i ≠ j → (F i)ᴴ*F j=0) :
    hsSq (∑ i, F i) = ∑ i, hsSq (F i) := by
  simp only [hsSq_eq_trace, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hF j i hji, Matrix.trace_zero, Complex.zero_re]
  · simp

variable [DecidableEq m]
end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma exists_common_bins {ι : Type u_ι} [Fintype ι] (A : ι → Matrix n n ℂ) (ε s : ℝ) :
    ∃ L : Finset ℤ, 0 ∈ L ∧ ∀ i, CoversBins L (A i) ε s := by
  classical
  let L := insert 0 (Finset.univ.biUnion (fun i =>
    (A i).finite_real_spectrum.toFinset.image (fun a => ⌊Real.log a/ε+s⌋)))
  refine ⟨L, Finset.mem_insert_self _ _, ?_⟩
  intro i a ha _
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  exact ⟨a, ((A i).finite_real_spectrum.mem_toFinset).mpr ha, rfl⟩

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

lemma prob_total (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) :
    ∑ a, ∑ b, prob C (P.effect a) (Q.effect b) = hsSq C := by
  simp_rw [← prob_sum_right, ← prob_sum_left, P.total, Q.total, prob_one]
lemma payoff_nonneg (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    0 ≤ payoff C P Q V := by
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  split
  · exact prob_nonneg (P.pos a) (Q.pos b)
  · exact le_rfl
lemma payoff_le_hsSq (C : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B) (V : A → B → Bool) :
    payoff C P Q V ≤ hsSq C := by
  rw [← prob_total C P Q]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  split
  · exact le_rfl
  · exact prob_nonneg (P.pos a) (Q.pos b)
end Payoff

section FilterMass
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {q : Type u_q} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

end FilterMass

open Filter Topology
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
lemma payoff_difference_le (C D : Matrix m n ℂ) (P : POVM m A) (Q : POVM n B)
    (V : A → B → Bool) (hC : hsSq C ≤ 1) (hD : hsSq D ≤ 1) :
    payoff C P Q V - payoff D P Q V ≤ 2*Real.sqrt (hsSq (C-D)) := by
  have hsc := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat C)).trans
    (le_trans (le_of_eq (hsSq_flat C)) hC)
  have hsd := (hsSq_mul_contraction (winSqrt_contraction P Q V) (flat D)).trans
    (le_trans (le_of_eq (hsSq_flat D)) hD)
  rw [payoff_eq_hsSq, payoff_eq_hsSq]
  refine (hsSq_difference_le _ _ hsc hsd).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  rw [← Matrix.mul_sub, ← flat_sub]
  exact (hsSq_mul_contraction (winSqrt_contraction P Q V) _).trans_eq (hsSq_flat _)
end WinEffect

lemma payoff_ratio_loss {w q a b c e : ℝ} (_he : 0 ≤ e) (hq : 0 ≤ q) (hqc : q ≤ c)
    (hca : c ≤ a) (hcb : c ≤ b) (ha : a ≤ 1) (hb : b ≤ 1)
    (hwq : w-q ≤ 2*Real.sqrt e) (hc : 1-c ≤ 2*Real.sqrt e) :
    w ≤ q/(a+b-c) + 4*Real.sqrt e := by
  have hc0 : 0 ≤ c := hq.trans hqc
  have hd0 : 0 ≤ a+b-c := by linarith
  by_cases hd : a+b-c = 0
  · have hq0 : q = 0 := by linarith
    rw [hq0, zero_div]
    rw [hq0, sub_zero] at hwq
    linarith [Real.sqrt_nonneg e]
  · have hdpos : 0 < a+b-c := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hr0 : 0 ≤ q/(a+b-c) := div_nonneg hq hd0
    have hr1 : q/(a+b-c) ≤ 1 := (div_le_one hdpos).mpr (by linarith)
    have hde : a+b-c ≤ 1+2*Real.sqrt e := by linarith
    have hm := mul_le_mul_of_nonneg_left hde hr0
    have hprod : q/(a+b-c)*(a+b-c) = q := div_mul_cancel₀ q hd
    rw [hprod] at hm
    have he' := Real.sqrt_nonneg e
    nlinarith

theorem filter_approximation_value {m n p q : Type} [Fintype m] [Fintype n]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
    [Nonempty n] [Nonempty q] {x y a b : ℕ} (G : Game x y a b)
    (D : Matrix n q ℂ) (hD : 0 < hsSq D)
    (M : Fin (x+1) → Matrix m p ℂ) (hM : ∀ x, hsSq (M x) = 1)
    (P : Fin (x+1) → POVM m (Fin (a+1))) (Q : Fin (y+1) → POVM p (Fin (b+1)))
    (K : Fin (x+1) → Matrix m n ℂ) (L : Fin (y+1) → Matrix p q ℂ)
    (hK : ∀ x, (K x)ᴴ*K x ≤ 1) (hL : ∀ y, (L y)ᴴ*L y ≤ 1)
    (hA : ∀ x, hsSq (K x*D) ≤ 1) (hB : ∀ y, hsSq (D*(L y)ᵀ) ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        hsSq (M z.1 - K z.1*D*(L z.2)ᵀ)) := by
  have hv := finite_filter_value_unnormalized G D hD P Q K L hK hL
  have hp : ∀ z : Fin (x+1) × Fin (y+1),
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2) ≤
        payoff (K z.1*D*(L z.2)ᵀ) (P z.1) (Q z.2) (G.accepts z.1 z.2) /
          (hsSq (K z.1*D)+hsSq (D*(L z.2)ᵀ)-hsSq (K z.1*D*(L z.2)ᵀ)) +
          4*Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) := by
    intro z
    obtain ⟨hca,hcb,_,_⟩ := filter_mass_bounds D (K z.1) (L z.2) (hK z.1) (hL z.2)
    apply payoff_ratio_loss (hsSq_nonneg _) (payoff_nonneg _ _ _ _) (payoff_le_hsSq _ _ _ _)
      hca hcb (hA z.1) (hB z.2)
    · exact payoff_difference_le _ _ _ _ _ (le_of_eq (hM z.1)) (hca.trans (hA z.1))
    · simpa only [hM z.1] using
        hsSq_difference_le (M z.1) (K z.1*D*(L z.2)ᵀ) (le_of_eq (hM z.1)) (hca.trans (hA z.1))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ =>
    mul_le_mul_of_nonneg_left (hp z) (G.questionProb_nonneg z))
  simp only [mul_add, Finset.sum_add_distrib] at hh
  have hroot := weighted_sqrt_le G.questionProb
    (fun z => hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) G.questionProb_nonneg
    (fun _ => hsSq_nonneg _) G.questionProb_sum
  have hfour : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (4*Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)))) =
      4*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        Real.sqrt (hsSq (M z.1-K z.1*D*(L z.2)ᵀ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [hfour] at hh
  linarith

section Blocks
variable {m : Type u_m} {n : Type u_n} {p : Type u_p} {ι : Type u_ι} [Fintype m] [Fintype n] [Fintype p] [Fintype ι]
omit [Fintype m] [Fintype n] [Fintype p] in
lemma rowBlocks_mul_transpose (F : ι → Matrix m n ℂ) (G : ι → Matrix p n ℂ) [Fintype n] :
    rowBlocks F * (rowBlocks G)ᵀ = ∑ l, F l*(G l)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, rowBlocks, Matrix.transpose_apply, Fintype.sum_prod_type,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
omit [Fintype m] [Fintype p] in
lemma rowBlocks_mul_diagonal [DecidableEq n] [DecidableEq ι]
    (F : ι → Matrix m n ℂ) (r : ι → ℝ) :
    rowBlocks F * Matrix.diagonal (fun j : n × ι => (r j.2 : ℂ)) =
      rowBlocks (fun l => r l • F l) := by
  ext i j
  simp only [Matrix.mul_diagonal, rowBlocks, Matrix.smul_apply, Complex.real_smul]
  ring
omit [Fintype p] in
lemma hsSq_rowBlocks (F : ι → Matrix m n ℂ) :
    hsSq (rowBlocks F) = ∑ l, hsSq (F l) := by
  simp only [hsSq, rowBlocks, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
omit [Fintype p] [Fintype ι] in
lemma hsSq_transpose (C : Matrix m n ℂ) : hsSq Cᵀ = hsSq C := by
  simp only [hsSq, Matrix.transpose_apply]
  exact Finset.sum_comm
omit [Fintype m] [Fintype p] [Fintype ι] in
lemma projectionRows_gram [DecidableEq ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ l, (P l).IsHermitian) (hPP : ∀ l, P l*P l = P l)
    (horth : ∀ l t, l ≠ t → P l*P t = 0) :
    (rowBlocks P)ᴴ*rowBlocks P = Matrix.blockDiagonal P := by
  ext ⟨i,l⟩ ⟨j,t⟩
  change ((P l)ᴴ*P t) i j = _
  rw [(hP l).eq]
  by_cases hlt : l = t
  · subst t
    rw [hPP l, Matrix.blockDiagonal_apply_eq]
  · rw [horth l t hlt]
    simp only [Matrix.zero_apply, Matrix.blockDiagonal_apply, ite_eq_right hlt]
omit [Fintype m] [Fintype p] in
lemma projectionRows_contraction [DecidableEq n] [DecidableEq ι] (P : ι → Matrix n n ℂ)
    (hP : ∀ l, (P l).IsHermitian) (hPP : ∀ l, P l*P l = P l)
    (horth : ∀ l t, l ≠ t → P l*P t = 0) : (rowBlocks P)ᴴ*rowBlocks P ≤ 1 := by
  rw [projectionRows_gram P hP hPP horth]
  apply projection_le_one
  · change (Matrix.blockDiagonal P)ᴴ = _
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1; funext l; exact (hP l).eq
  · rw [← Matrix.blockDiagonal_mul]
    congr 1; funext l; exact hPP l
end Blocks

section Resource
variable {n : Type u_n} [Fintype n] [DecidableEq n]
lemma bobBinFilter_contraction (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ) :
    (bobBinFilter L N ε s)ᴴ*bobBinFilter L N ε s ≤ 1 := by
  apply projectionRows_contraction
  · intro l; exact (binProjection_hermitian _ _ _ _).transpose
  · intro l
    rw [← Matrix.transpose_mul, binProjection_sq (rightAbs_pos N).isHermitian]
  · intro l t hlt
    rw [← Matrix.transpose_mul,
      binProjection_orthogonal (rightAbs_pos N).isHermitian ε s (Subtype.coe_ne_coe.mpr (Ne.symm hlt)),
      Matrix.transpose_zero]
omit [Fintype n] in
lemma binResource_transpose (L : Finset ℤ) (ε s : ℝ) :
    (binResource (n := n) L ε s)ᵀ = binResource (n := n) L ε s := Matrix.diagonal_transpose _
lemma binResource_pos [Nonempty n] (L : Finset ℤ) [Nonempty L] (ε s : ℝ) :
    0 < hsSq (binResource (n := n) L ε s) := by
  simp only [hsSq, binResource, Matrix.diagonal_apply, apply_ite Complex.normSq,
    Complex.normSq_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Complex.normSq_ofReal]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · exact ⟨(Classical.choice ‹Nonempty n›, Classical.choice ‹Nonempty L›), Finset.mem_univ _,
      mul_pos (Real.exp_pos _) (Real.exp_pos _)⟩
lemma bin_output (L : Finset ℤ) (M N : Matrix n n ℂ) (ε s : ℝ) :
    binFilter L M ε s * binResource (n := n) L ε s * (bobBinFilter L N ε s)ᵀ =
      polar M*crossBins L (rightAbs M) (rightAbs N) ε s := by
  change rowBlocks (fun l : L => polar M*binProjection (rightAbs M) ε s l) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ)) *
    (rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ))ᵀ = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), rowBlocks_mul_transpose]
  simp only [Matrix.transpose_transpose, Matrix.smul_mul, crossBins, Matrix.mul_sum,
    Matrix.mul_smul, Matrix.mul_assoc]
lemma hsSq_polar_bin (M : Matrix n n ℂ) (ε s : ℝ) (l : ℤ) :
    hsSq (polar M*binProjection (rightAbs M) ε s l) =
      hsSq (binProjection (rightAbs M) ε s l) := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (polar M)ᴴ (polar M), polar_gram_bin]
lemma hsSq_roundedAbs_eq_sum (L : Finset ℤ) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (ε s : ℝ) (hL : CoversBins L A ε s) :
    hsSq (roundedAbs A ε s) = ∑ l : L, (binScale ε s l)^2*hsSq (binProjection A ε s l) := by
  rw [roundedAbs_eq_sum L ε s hL, hsSq_sum_orthogonal]
  · simp only [hsSq_smul]
  · intro l t hlt
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      (binProjection_hermitian A ε s l).eq]
    rw [binProjection_orthogonal hA ε s (Subtype.coe_ne_coe.mpr hlt), smul_zero, smul_zero]
lemma bin_left_mass (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ)
    (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (binFilter L M ε s*binResource (n := n) L ε s) = hsSq (roundedAbs (rightAbs M) ε s) := by
  change hsSq (rowBlocks (fun l : L => polar M*binProjection (rightAbs M) ε s l) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ))) = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), hsSq_rowBlocks, hsSq_roundedAbs_eq_sum L (rightAbs_pos M).isHermitian ε s hL]
  simp only [hsSq_smul, hsSq_polar_bin]
lemma bin_right_mass (L : Finset ℤ) (N : Matrix n n ℂ) (ε s : ℝ)
    (hL : CoversBins L (rightAbs N) ε s) :
    hsSq (binResource (n := n) L ε s*(bobBinFilter L N ε s)ᵀ) = hsSq (roundedAbs (rightAbs N) ε s) := by
  rw [← hsSq_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, binResource_transpose]
  change hsSq (rowBlocks (fun l : L => (binProjection (rightAbs N) ε s l)ᵀ) *
    Matrix.diagonal (fun j : n × L => (binScale ε s j.2 : ℂ))) = _
  rw [rowBlocks_mul_diagonal _ (fun l : L => binScale ε s l), hsSq_rowBlocks, hsSq_roundedAbs_eq_sum L (rightAbs_pos N).isHermitian ε s hL]
  simp only [hsSq_smul, hsSq_transpose]
end Resource

theorem correlated_sampling_value {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {x y a b : ℕ} (G : Game x y a b)
    (M : Fin (x+1) → Matrix n n ℂ) (N : Fin (y+1) → Matrix n n ℂ)
    (hM : ∀ x, hsSq (M x) = 1) (hN : ∀ y, hsSq (N y) = 1)
    (P : Fin (x+1) → POVM n (Fin (a+1))) (Q : Fin (y+1) → POVM n (Fin (b+1)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      payoff (M z.1) (P z.1) (Q z.2) (G.accepts z.1 z.2)) ≤ entangledValue G +
      4*Real.sqrt (2*ε^2+(12/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) := by
  have hMA : ∀ x, hsSq (rightAbs (M x)) = 1 := fun x => (hsSq_sqrt_gram (M x)).trans (hM x)
  have hNA : ∀ y, hsSq (rightAbs (N y)) = 1 := fun y => (hsSq_sqrt_gram (N y)).trans (hN y)
  obtain ⟨s,hs⟩ := exists_shift_spectralEnvelope_le G.questionProb G.questionProb_nonneg
    G.questionProb_sum (fun z => rightAbs (M z.1)) (fun z => rightAbs (N z.2))
    (fun z => rightAbs_pos (M z.1)) (fun z => rightAbs_pos (N z.2))
    (fun z => hMA z.1) (fun z => hNA z.2) hε hε1
  obtain ⟨L,hL0,hL⟩ := exists_common_bins
    (Sum.elim (fun x => rightAbs (M x)) (fun y => rightAbs (N y))) ε s
  let : Nonempty L := ⟨⟨0,hL0⟩⟩
  have hLM : ∀ x, CoversBins L (rightAbs (M x)) ε s := fun x => hL (Sum.inl x)
  have hLN : ∀ y, CoversBins L (rightAbs (N y)) ε s := fun y => hL (Sum.inr y)
  have hleft : ∀ x, hsSq (binFilter L (M x) ε s*binResource (n := n) L ε s) ≤ 1 := by
    intro x
    rw [bin_left_mass L (M x) ε s (hLM x)]
    exact (roundedAbs_energy_le (rightAbs_pos (M x)) hε s).trans_eq (hMA x)
  have hright : ∀ y, hsSq (binResource (n := n) L ε s*(bobBinFilter L (N y) ε s)ᵀ) ≤ 1 := by
    intro y
    rw [bin_right_mass L (N y) ε s (hLN y)]
    exact (roundedAbs_energy_le (rightAbs_pos (N y)) hε s).trans_eq (hNA y)
  have hv := filter_approximation_value G (binResource (n := n) L ε s) (binResource_pos L ε s)
    M hM P Q (fun x => binFilter L (M x) ε s) (fun y => bobBinFilter L (N y) ε s)
    (fun x => binFilter_contraction L (M x) ε s)
    (fun y => bobBinFilter_contraction L (N y) ε s) hleft hright
  apply hv.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (show (0 : ℝ) ≤ 4 by norm_num)
  apply Real.sqrt_le_sqrt
  simp only [bin_output]
  have he : ∀ z : Fin (x+1) × Fin (y+1),
      hsSq (M z.1-polar (M z.1)*crossBins L (rightAbs (M z.1)) (rightAbs (N z.2)) ε s) ≤
      2*ε^2 + 2*spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
        (rightAbs_pos (N z.2)).isHermitian ε s := by
    intro z
    have herr := polar_crossBins_error_le L (M z.1) (N z.2) hε s (hLM z.1)
    rw [hM z.1, mul_one] at herr
    have hmis := binProjection_mismatch_le L (rightAbs_pos (M z.1)) (rightAbs_pos (N z.2)) hε s
    rw [← Finset.sum_coe_sort L] at hmis
    change binMismatch L _ _ ε s ≤ _ at hmis
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun z _ => mul_le_mul_of_nonneg_left (he z) (G.questionProb_nonneg z))
  have heq : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      (2*ε^2+2*spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
        (rightAbs_pos (N z.2)).isHermitian ε s)) =
      2*ε^2 + 2*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
        spectralEnvelope (rightAbs_pos (M z.1)).isHermitian
          (rightAbs_pos (N z.2)).isHermitian ε s := by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, G.questionProb_sum, one_mul, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro z _; ring
  rw [heq] at hsum
  have habs : (∑ z : Fin (x+1) × Fin (y+1), G.questionProb z *
      hsSq (rightAbs (M z.1)-rightAbs (N z.2))) ≤
      2*∑ z : Fin (x+1) × Fin (y+1), G.questionProb z * hsSq (M z.1-N z.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro z _
    have hh := mul_le_mul_of_nonneg_left (hsSq_right_absolute_sub_le (M z.1) (N z.2))
      (G.questionProb_nonneg z)
    dsimp [rightAbs]
    convert hh using 1
    ring
  have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt habs) (show 0 ≤ 6/ε by positivity)
  have hh' := hs.trans hh
  calc
    _ ≤ 2*ε^2 + 2*((6/ε)*Real.sqrt (2*∑ z : Fin (x+1) × Fin (y+1),
        G.questionProb z * hsSq (M z.1-N z.2))) :=
      hsum.trans (add_le_add_right (mul_le_mul_of_nonneg_left hh' (by norm_num)) _)
    _ = _ := by ring
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
open scoped BigOperators MatrixOrder ComplexOrder Kronecker
open Matrix


theorem solution : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.correlated_sampling_value := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.correlated_sampling_value
