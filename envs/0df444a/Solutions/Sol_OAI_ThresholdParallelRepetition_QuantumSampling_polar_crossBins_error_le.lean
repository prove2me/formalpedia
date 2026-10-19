-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.polar_crossBins_error_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:55:24.622868+00:00
-- url     : https://prove2.me/submissions/e0ad0d29-c467-4512-91d0-2e3194b5b88f

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CoherentFilters.lean:L320-L339
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.polar_crossBins_error_le. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_MeasurementTransport_self_mul_supportInverse_mul
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_hsSq_cfc_eq
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_polar_gram
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_roundedAbs_eq_sum
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_sub_binWeight_le

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

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling

lemma binIndicator_sq (ε s : ℝ) (l : ℤ) (a : ℝ) : (binIndicator ε s l a)^2 = binIndicator ε s l a := by
  unfold binIndicator; split <;> norm_num
lemma binIndicator_mul_ne (ε s : ℝ) {l k : ℤ} (hlk : l ≠ k) (a : ℝ) :
    binIndicator ε s l a * binIndicator ε s k a = 0 := by
  unfold binIndicator
  split_ifs <;> simp_all

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
lemma rightAbs_sq (M : Matrix m n ℂ) : rightAbs M * rightAbs M = Mᴴ*M :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg

lemma supportInverse_mul_le_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    supportInverse A * A ≤ 1 := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA
  change cfc (fun t : ℝ => t⁻¹) A * A ≤ 1
  calc
    _ = cfc (fun t : ℝ => t⁻¹*t) A := by
      calc
        _ = cfc (fun t : ℝ => t⁻¹) A * cfc (fun t : ℝ => t) A := by rw [hid]
        _ = _ := by
          erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    _ ≤ 1 := cfc_le_one _ A (by intro t _; by_cases ht : t = 0 <;> simp [ht])

lemma polar_contraction (M : Matrix m n ℂ) : (polar M)ᴴ*polar M ≤ 1 := by
  rw [polar_gram]
  exact supportInverse_mul_le_one (rightAbs_pos M).isHermitian

lemma polar_mul_rightAbs (M : Matrix m n ℂ) : polar M * rightAbs M = M := by
  let A := rightAbs M
  let D := supportInverse A
  have hA : A.IsHermitian := (rightAbs_pos M).isHermitian
  have hzero : (Mᴴ*M)*(1-D*A) = 0 := by
    rw [← rightAbs_sq M]
    change (A*A)*(1-D*A)=0
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      self_mul_supportInverse_mul hA, sub_self, Matrix.mul_zero]
  have hz := (Matrix.conjTranspose_mul_self_mul_eq_zero M (1-D*A)).mp hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hz
  simpa only [polar, Matrix.mul_assoc] using hz.symm

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

lemma roundedAbs_error_le {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) : hsSq (A-roundedAbs A ε s) ≤ ε^2*hsSq A := by
  have hid : cfc (fun t : ℝ => t) A = A := cfc_id' ℝ A hA.isHermitian
  have he : A-roundedAbs A ε s = cfc (fun a => a-binWeight a ε s) A := by
    erw [cfc_sub (fun t : ℝ => t) (fun a => binWeight a ε s) A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
    rw [hid]; rfl
  rw [he, hsSq_cfc_eq hA.isHermitian, hsSq_eq_sum_eigenvalues_sq hA.isHermitian, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h1 := binWeight_le (hA.eigenvalues_nonneg i) hε s
  have h2 := sub_binWeight_le (hA.eigenvalues_nonneg i) hε s
  have h3 : 0 ≤ ε * hA.isHermitian.eigenvalues i := mul_nonneg hε.le (hA.eigenvalues_nonneg i)
  nlinarith [sq_nonneg (hA.isHermitian.eigenvalues i-binWeight (hA.isHermitian.eigenvalues i) ε s-ε*hA.isHermitian.eigenvalues i)]

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
lemma hsSq_mul_projection_le {P : Matrix m m ℂ} (hP : P.IsHermitian) (hPP : P*P=P)
    (M : Matrix m n ℂ) : hsSq (P*M) ≤ hsSq M := by
  apply hsSq_mul_contraction
  rw [hP.eq, hPP]
  exact projection_le_one hP hPP

omit [DecidableEq m] in

lemma hsSq_orthogonal_projection_sum {ι : Type u_ι} [Fintype ι] [DecidableEq ι]
    (P : ι → Matrix m m ℂ) (F : ι → Matrix m n ℂ) (r : ι → ℝ)
    (hP : ∀ i, (P i).IsHermitian) (hPP : ∀ i j, i ≠ j → P i*P j=0) :
    hsSq (∑ i, r i • (P i*F i)) = ∑ i, (r i)^2*hsSq (P i*F i) := by
  rw [hsSq_sum_orthogonal]
  · simp only [hsSq_smul]
  · intro i j hij
    simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
      (hP i).eq, Matrix.smul_mul, Matrix.mul_smul]
    rw [show ((F i)ᴴ*P i)*(P j*F j)=(F i)ᴴ*(P i*P j)*F j by simp only [Matrix.mul_assoc],
      hPP i j hij, Matrix.mul_zero, Matrix.zero_mul, smul_zero, smul_zero]

end ThresholdParallelRepetition.QuantumSampling

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition.QuantumSampling
variable {n : Type u_n} [Fintype n] [DecidableEq n]

lemma crossBins_error_le (L : Finset ℤ) {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (_hB : B.IsHermitian) (ε s : ℝ) (hL : CoversBins L A ε s) :
    hsSq (roundedAbs A ε s-crossBins L A B ε s) ≤ binMismatch L A B ε s := by
  have he : roundedAbs A ε s-crossBins L A B ε s =
      ∑ l : L, binScale ε s l • (binProjection A ε s l * (binProjection A ε s l-binProjection B ε s l)) := by
    rw [roundedAbs_eq_sum L ε s hL, crossBins, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.mul_sub, binProjection_sq hA, smul_sub]
  rw [he, hsSq_orthogonal_projection_sum _ _ _ (fun _ => binProjection_hermitian _ _ _ _)
    (fun i j hij => binProjection_orthogonal hA ε s (Subtype.coe_ne_coe.mpr hij))]
  unfold binMismatch
  apply Finset.sum_le_sum; intro l _
  exact mul_le_mul_of_nonneg_left
    (hsSq_mul_projection_le (binProjection_hermitian _ _ _ _) (binProjection_sq hA ε s l) _) (sq_nonneg _)

lemma polar_crossBins_error_le (L : Finset ℤ) (M N : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) (s : ℝ) (hL : CoversBins L (rightAbs M) ε s) :
    hsSq (M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s) ≤
      2*ε^2*hsSq M + 2*binMismatch L (rightAbs M) (rightAbs N) ε s := by
  have hm : M-polar M*crossBins L (rightAbs M) (rightAbs N) ε s =
      polar M*(rightAbs M-roundedAbs (rightAbs M) ε s) +
      polar M*(roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s) := by
    simp only [Matrix.mul_sub, polar_mul_rightAbs]
    abel
  rw [hm]
  have h1 := hsSq_mul_contraction (polar_contraction M) (rightAbs M-roundedAbs (rightAbs M) ε s)
  have h2 := hsSq_mul_contraction (polar_contraction M)
    (roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s)
  have h3 := roundedAbs_error_le (rightAbs_pos M) hε s
  have h4 := crossBins_error_le L (rightAbs_pos M).isHermitian (rightAbs_pos N).isHermitian ε s hL
  have h5 : hsSq (rightAbs M) = hsSq M := hsSq_sqrt_gram M
  rw [h5] at h3
  have h6 := hsSq_add_le (polar M*(rightAbs M-roundedAbs (rightAbs M) ε s))
    (polar M*(roundedAbs (rightAbs M) ε s-crossBins L (rightAbs M) (rightAbs N) ε s))
  linarith

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
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.polar_crossBins_error_le.{u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.polar_crossBins_error_le.{u_n}
