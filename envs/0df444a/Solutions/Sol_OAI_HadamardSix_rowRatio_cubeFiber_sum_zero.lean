-- Prove2me | solution 1 for OAI.HadamardSix.rowRatio_cubeFiber_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:31:01.887924+00:00
-- url     : https://prove2.me/submissions/b5c99c2c-e6a3-451b-bed2-5cbd7c972402

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Hadamard/CubeFibers.lean:L175-L181
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.HadamardSix.rowRatio_cubeFiber_sum_zero.
-- The statement is the platform stub (Theorems.Thm_OAI_HadamardSix_rowRatio_cubeFiber_sum_zero) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_HadamardCubeFiber
import Definitions.Def_OAI_LinearAlgebra_Hadamard_Polynomials
import Definitions.Def_OAI_LinearAlgebra_Hadamard_CubeFibers
import Theorems.Thm_OAI_HadamardSix_fourth_power_sum_zero

-- ---- inline helpers from OAI.LinearAlgebra.Hadamard.Basic ----
namespace OAI

/-! Unit entries, orthogonality, characters and the cubic matrix. -/

open scoped BigOperators Matrix

namespace HadamardSix

lemma IsComplexHadamard.mul_conjTranspose {H : Matrix6} (hH : IsComplexHadamard H) :
    H * H.conjTranspose = (6 : ℂ) • (1 : Matrix6) := by
  have hleft : ((6 : ℂ)⁻¹ • H.conjTranspose) * H = 1 := by
    rw [Matrix.smul_mul, hH.2, smul_smul]
    norm_num
  have hright := mul_eq_one_comm.mp hleft
  rw [Matrix.mul_smul] at hright
  have h := congrArg (fun K : Matrix6 => (6 : ℂ) • K) hright
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul] using h

lemma IsComplexHadamard.row_orthogonality {H : Matrix6} (hH : IsComplexHadamard H)
    (i j : Index) :
    ∑ k, H i k * star (H j k) = if i = j then 6 else 0 := by
  have h := congr_fun (congr_fun hH.mul_conjTranspose i) j
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] using h

end HadamardSix

end OAI

-- ---- inline helpers from OAI.LinearAlgebra.Hadamard.CubeFibers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Cubic values, their multiplicities, and cancellation on each fibre. -/

open scoped BigOperators Matrix

namespace HadamardSix

lemma ratio_cubeFiber_sum_zero (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0)
    (a b : ℂ) (hne : a ≠ b) (hab : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b) :
    ∑ i ∈ cubeFiber v a, v i = 0 := by
  classical
  have hf : (∑ i ∈ cubeFiber v a, v i ^ 4) = a * ∑ i ∈ cubeFiber v a, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← (mem_cubeFiber v a i).mp hi]
    ring
  have hl : (∑ i ∈ (cubeFiber v a)ᶜ, v i ^ 4) = b * ∑ i ∈ (cubeFiber v a)ᶜ, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← (hab i).resolve_left (by simpa using hi)]
    ring
  have h4 := fourth_power_sum_zero v hv h1 h2
  rw [← Finset.sum_add_sum_compl (cubeFiber v a), hf, hl] at h4
  rw [← Finset.sum_add_sum_compl (cubeFiber v a)] at h1
  have he : (a - b) * ∑ i ∈ cubeFiber v a, v i = 0 := by
    linear_combination h4 - b * h1
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)

lemma rowRatio_norm {H : Matrix6} (hu : Unimodular H) (i j k : Index) :
    ‖rowRatio H i j k‖ = 1 := by simp [rowRatio, hu i k, hu j k]

lemma rowRatio_first_sum {H : Matrix6} (hH : IsComplexHadamard H)
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k = 0 := by
  simpa only [rowRatio, ite_eq_right hij] using hH.row_orthogonality i j

lemma rowRatio_second_sum {H : Matrix6} (hs : IsComplexHadamard (entrywiseSquare H))
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k ^ 2 = 0 := by
  simpa only [rowRatio, entrywiseSquare, mul_pow, star_pow, ite_eq_right hij]
    using hs.row_orthogonality i j

end HadamardSix

end OAI

-- ---- hoisted mission target ----
open OAI OAI.HadamardSix
open scoped BigOperators Matrix

theorem solution {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j)
    (a b : ℂ) (hne : a ≠ b)
    (hab : ∀ k, rowRatio H i j k ^ 3 = a ∨ rowRatio H i j k ^ 3 = b) :
    ∑ k ∈ cubeFiber (rowRatio H i j) a, H i k * star (H j k) = 0 :=
  ratio_cubeFiber_sum_zero (rowRatio H i j) (rowRatio_norm hH.1 i j)
    (rowRatio_first_sum hH hij) (rowRatio_second_sum hs hij) a b hne hab
