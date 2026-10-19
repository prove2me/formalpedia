-- Prove2me | solution 1 for OAI.ThresholdParallelRepetition.QuantumSampling.binFilter_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:52:08.145514+00:00
-- url     : https://prove2.me/submissions/413714f7-7868-4975-9f09-12f3208d3bd2

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/CoherentFilters.lean:L149-L161
-- (upload_full_project.md Phase 4): solution for node OAI.ThresholdParallelRepetition.QuantumSampling.binFilter_contraction. The node keeps its source
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
import Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_polar_gram

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
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma binFilter_gram (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s =
      Matrix.blockDiagonal (fun l : L => binProjection (rightAbs M) ε s l) := by
  ext ⟨i,l⟩ ⟨j,k⟩
  change (((polar M * binProjection (rightAbs M) ε s l)ᴴ *
    (polar M * binProjection (rightAbs M) ε s k)) i j) = _
  rw [Matrix.conjTranspose_mul, (binProjection_hermitian _ _ _ _).eq]
  rw [show (binProjection (rightAbs M) ε s l * (polar M)ᴴ) *
      (polar M * binProjection (rightAbs M) ε s k) =
      binProjection (rightAbs M) ε s l * (((polar M)ᴴ*polar M)*binProjection (rightAbs M) ε s k)
      by simp only [Matrix.mul_assoc], polar_gram_bin]
  by_cases hlk : l = k
  · subst k
    rw [binProjection_sq (rightAbs_pos M).isHermitian]
    exact (Matrix.blockDiagonal_apply_eq (fun l : L => binProjection (rightAbs M) ε s l) i j l).symm
  · rw [binProjection_orthogonal (rightAbs_pos M).isHermitian ε s (Subtype.coe_ne_coe.mpr hlk)]
    simp only [Matrix.zero_apply, Matrix.blockDiagonal_apply, ite_eq_right hlk]

lemma binFilter_contraction (L : Finset ℤ) (M : Matrix n n ℂ) (ε s : ℝ) :
    (binFilter L M ε s)ᴴ * binFilter L M ε s ≤ 1 := by
  rw [binFilter_gram]
  apply projection_le_one
  · change (Matrix.blockDiagonal (fun l : L => binProjection (rightAbs M) ε s l))ᴴ = _
    rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext l
    exact (binProjection_hermitian _ _ _ _).eq
  · rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext l
    exact binProjection_sq (rightAbs_pos M).isHermitian ε s l

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
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix


theorem solution.{u_n} : type_of% @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.binFilter_contraction.{u_n} := @_root_.OAI.ThresholdParallelRepetition.QuantumSampling.binFilter_contraction.{u_n}
