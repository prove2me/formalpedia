-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:25:57.966727+00:00
-- url     : https://prove2.me/submissions/aa2f105a-f381-474d-9e64-0bfd201ac384

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz

section
set_option autoImplicit false
namespace IsingVectorBalancing.Subgaussian.Dev.L6
open IsingVectorBalancing.Subgaussian

theorem quad {C : Type*} [Fintype C] {d : ℕ} (u : C → Vec d) (z : C → ℝ) :
    z ⬝ᵥ (lorentzMatrix u).mulVec z = (∑ c, z c) ^ 2 - ‖∑ c, z c • u c‖ ^ 2 := by
  have h1 : ‖∑ c, z c • u c‖ ^ 2 = ∑ c, ∑ c', z c * z c' * inner ℝ (u c) (u c') := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have h2 : (∑ c, z c) ^ 2 = ∑ c, ∑ c', z c * z c' := by
    rw [sq, Finset.sum_mul_sum]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  simp only [dotProduct, Matrix.mulVec, lorentzMatrix, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
  ring

theorem eig_dot {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (i j : C) : (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = if i = j then 1 else 0 := by
  have := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [dotProduct_comm] using this

theorem lorentzian_of_quad {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ}
    (hA : A.IsHermitian) (hq : ∀ z : C → ℝ, ∑ c, z c = 0 → z ⬝ᵥ A.mulVec z ≤ 0) :
    (Finset.univ.filter (fun c => 0 < hA.eigenvalues c)).card ≤ 1 := by
  by_contra hcon
  rw [not_le, Finset.one_lt_card] at hcon
  obtain ⟨c1, h1, c2, h2, hne⟩ := hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  set e1 : C → ℝ := ⇑(hA.eigenvectorBasis c1) with he1
  set e2 : C → ℝ := ⇑(hA.eigenvectorBasis c2) with he2
  have m1 : A.mulVec e1 = hA.eigenvalues c1 • e1 := hA.mulVec_eigenvectorBasis c1
  have m2 : A.mulVec e2 = hA.eigenvalues c2 • e2 := hA.mulVec_eigenvectorBasis c2
  have d11 : e1 ⬝ᵥ e1 = 1 := by rw [he1, eig_dot]; simp
  have d22 : e2 ⬝ᵥ e2 = 1 := by rw [he2, eig_dot]; simp
  have d12 : e1 ⬝ᵥ e2 = 0 := by rw [he1, he2, eig_dot]; simp [hne]
  have d21 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact d12
  obtain ⟨a, b, hab, hs⟩ : ∃ a b : ℝ, (0 < a ^ 2 + b ^ 2) ∧
      a * ∑ c, e1 c + b * ∑ c, e2 c = 0 := by
    by_cases hs1 : ∑ c, e1 c = 0
    · exact ⟨1, 0, by norm_num, by simp [hs1]⟩
    · refine ⟨∑ c, e2 c, -∑ c, e1 c, ?_, by ring⟩
      have : 0 < (∑ c, e1 c) ^ 2 := by positivity
      nlinarith [sq_nonneg (∑ c, e2 c)]
  set z : C → ℝ := a • e1 + b • e2 with hz
  have hsum : ∑ c, z c = 0 := by
    simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    exact hs
  have hmul : A.mulVec z = a • (hA.eigenvalues c1 • e1) + b • (hA.eigenvalues c2 • e2) := by
    rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, m1, m2]
  have hval : z ⬝ᵥ A.mulVec z = a ^ 2 * hA.eigenvalues c1 + b ^ 2 * hA.eigenvalues c2 := by
    rw [hmul, hz]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, d11, d22, d12,
      d21, smul_eq_mul]
    ring
  have := hq z hsum
  rw [hval] at this
  have p1 := mul_nonneg (sq_nonneg a) h1.le
  have p2 := mul_nonneg (sq_nonneg b) h2.le
  rcases lt_or_ge 0 (a ^ 2) with ha | ha
  · nlinarith [mul_pos ha h1]
  · have : 0 < b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
    nlinarith [mul_pos this h2]

end IsingVectorBalancing.Subgaussian.Dev.L6

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.L6 in
theorem chk_lemma_6 {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}
    (u : C → Vec d) (hu : ∀ c, ‖u c‖ ≤ 1) :
    IsLorentzian (lorentzMatrix u) := by
  have hH : (lorentzMatrix u).IsHermitian := by
    ext i j
    simp [lorentzMatrix, Matrix.conjTranspose_apply, real_inner_comm]
  refine ⟨fun c c' => ?_, hH, lorentzian_of_quad hH fun z hz => ?_⟩
  · have := (real_inner_le_norm (u c) (u c')).trans
      (mul_le_one₀ (hu c) (norm_nonneg _) (hu c'))
    simp only [lorentzMatrix]; linarith
  · rw [quad, hz]; nlinarith [sq_nonneg ‖∑ c, z c • u c‖]

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_lemma_6 := @IsingVectorBalancing.Subgaussian.chk_lemma_6
