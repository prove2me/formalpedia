-- Prove2me | solution 1 for MatrixSpectral.eigenvalue_count_le_add_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:27:06.540991+00:00
-- url     : https://prove2.me/submissions/5b1868cf-7944-4e98-b199-6b4f613406a1

import Mathlib

open scoped Matrix

namespace MatrixSpectralAux
open Matrix

variable {d : ℕ}

lemma quad_conj (U : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    star x ⬝ᵥ ((U * B * star U) *ᵥ x) = star (star U *ᵥ x) ⬝ᵥ (B *ᵥ (star U *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  simp [Matrix.star_eq_conjTranspose]

lemma quad_re_self {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re =
      ∑ i, hA.eigenvalues i * ‖(star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i‖^2 := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, quad_conj]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum, Function.comp_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  set y := (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma normsq_U {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (x : Fin d → ℂ) :
    ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) i‖^2 = (star x ⬝ᵥ x).re := by
  have hU : star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
  have h1 : star (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) ⬝ᵥ
      (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) = star x ⬝ᵥ x := by
    have := quad_conj (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) 1 x
    rw [Matrix.mul_one, Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2, one_mulVec,
      one_mulVec] at this
    exact this.symm
  rw [← h1]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Complex.mul_re, Complex.sq_norm, Complex.normSq_apply]


def ext (A : Finset (Fin d)) (c : A → ℂ) : Fin d → ℂ := fun i => if h : i ∈ A then c ⟨i, h⟩ else 0

def psi (W : Matrix (Fin d) (Fin d) ℂ) (A : Finset (Fin d)) : (A → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun c := W *ᵥ ext A c
  map_add' c c' := by
    rw [← mulVec_add]; congr 1; funext i; by_cases h : i ∈ A <;> simp [ext, h]
  map_smul' a c := by
    rw [RingHom.id_apply, ← mulVec_smul]; congr 1; funext i; by_cases h : i ∈ A <;> simp [ext, h]

lemma psi_inv {W : Matrix (Fin d) (Fin d) ℂ} (hW : star W * W = 1) (A : Finset (Fin d)) (c : A → ℂ) :
    star W *ᵥ psi W A c = ext A c := by
  show star W *ᵥ (W *ᵥ ext A c) = ext A c
  rw [mulVec_mulVec, hW, one_mulVec]

lemma psi_finrank {W : Matrix (Fin d) (Fin d) ℂ} (hW : star W * W = 1) (A : Finset (Fin d)) :
    Module.finrank ℂ (LinearMap.range (psi W A)) = A.card := by
  have hinj : Function.Injective (psi W A) := by
    intro c c' h
    have h2 := congrArg (fun x => star W *ᵥ x) h
    simp only [psi_inv hW] at h2
    funext ⟨i, hi⟩
    have := congrFun h2 i
    simpa [ext, hi] using this
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  simp

lemma dim_lemma (S T K : Submodule ℂ (Fin d → ℂ))
    (h : 2 * d < Module.finrank ℂ S + Module.finrank ℂ T + Module.finrank ℂ K) :
    ∃ x, x ≠ 0 ∧ x ∈ S ∧ x ∈ T ∧ x ∈ K := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S T
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ T) K
  have hd : ∀ P : Submodule ℂ (Fin d → ℂ), Module.finrank ℂ P ≤ d := fun P => by
    have := Submodule.finrank_le P; simpa using this
  have h3 := hd (S ⊔ T)
  have h4 := hd ((S ⊓ T) ⊔ K)
  have hpos : 0 < Module.finrank ℂ ((S ⊓ T ⊓ K : Submodule ℂ (Fin d → ℂ))) := by omega
  have hne : (S ⊓ T ⊓ K : Submodule ℂ (Fin d → ℂ)) ≠ ⊥ := by
    intro hb; rw [hb, finrank_bot] at hpos; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨x, hx0, hx.1.1, hx.1.2, hx.2⟩

lemma ker_finrank (M : Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (LinearMap.ker M.mulVecLin) = d - M.rank := by
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  simp only [Module.finrank_fin_fun] at this
  rw [Matrix.rank]; omega

/-- quadratic form on an eigen-coordinate subspace -/
lemma quad_sub {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (I : Finset (Fin d)) (c : I → ℂ) :
    (star (psi (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) I c) ⬝ᵥ
      (A *ᵥ psi (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) I c)).re =
      ∑ i, hA.eigenvalues i * ‖ext I c i‖^2 ∧
    (star (psi (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) I c) ⬝ᵥ
      psi (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) I c).re = ∑ i, ‖ext I c i‖^2 := by
  have hW : star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2
  constructor
  · rw [quad_re_self hA, psi_inv hW]
  · rw [← normsq_U hA, psi_inv hW]

theorem main_le {U V : Matrix (Fin d) (Fin d) ℂ} (hU : U.IsHermitian) (hV : V.IsHermitian)
    (A B : Finset (Fin d)) (t : ℝ)
    (hA : ∀ i ∈ A, hU.eigenvalues i ≤ t) (hB : ∀ j ∈ B, t < hV.eigenvalues j) :
    A.card + B.card ≤ d + (U - V).rank := by
  by_contra hcon
  push Not at hcon
  have hrk : (U - V).rank ≤ d := by
    have := Matrix.rank_le_card_width (U - V); simpa using this
  set WU := (hU.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  set WV := (hV.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hWU : star WU * WU = 1 := Unitary.star_mul_self_of_mem (hU.eigenvectorUnitary).2
  have hWV : star WV * WV = 1 := Unitary.star_mul_self_of_mem (hV.eigenvectorUnitary).2
  obtain ⟨x, hx0, hxS, hxT, hxK⟩ := dim_lemma (LinearMap.range (psi WU A))
    (LinearMap.range (psi WV B)) (LinearMap.ker (U - V).mulVecLin) (by
      rw [psi_finrank hWU, psi_finrank hWV, ker_finrank]; omega)
  obtain ⟨c, rfl⟩ := hxS
  obtain ⟨c', hc'⟩ := hxT
  have hUV : U *ᵥ psi WU A c = V *ᵥ psi WU A c := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, sub_mulVec, sub_eq_zero] at hxK; exact hxK
  obtain ⟨qU, nU⟩ := quad_sub hU A c
  obtain ⟨qV, nV⟩ := quad_sub hV B c'
  rw [hc'] at qV nV
  -- upper bound
  have h1 : (star (psi WU A c) ⬝ᵥ (U *ᵥ psi WU A c)).re ≤ t * (star (psi WU A c) ⬝ᵥ psi WU A c).re := by
    rw [qU, nU, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : i ∈ A
    · exact mul_le_mul_of_nonneg_right (hA i hi) (sq_nonneg _)
    · simp [ext, hi]
  -- strict lower bound
  have hne : ∃ j ∈ B, ext B c' j ≠ 0 := by
    by_contra hall; push Not at hall
    apply hx0
    rw [← hc']
    show WV *ᵥ ext B c' = 0
    have : ext B c' = 0 := by
      funext j; by_cases hj : j ∈ B
      · exact hall j hj
      · simp [ext, hj]
    rw [this, mulVec_zero]
  have h2 : t * (star (psi WU A c) ⬝ᵥ psi WU A c).re < (star (psi WU A c) ⬝ᵥ (V *ᵥ psi WU A c)).re := by
    rw [qV, nV, Finset.mul_sum]
    obtain ⟨j, hjB, hj0⟩ := hne
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i ∈ B
      · exact mul_le_mul_of_nonneg_right (hB i hi).le (sq_nonneg _)
      · simp [ext, hi]
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_right (hB j hjB) (by positivity)⟩
  rw [hUV] at h1
  linarith

theorem main_ge {U V : Matrix (Fin d) (Fin d) ℂ} (hU : U.IsHermitian) (hV : V.IsHermitian)
    (A B : Finset (Fin d)) (t : ℝ)
    (hA : ∀ i ∈ A, t ≤ hU.eigenvalues i) (hB : ∀ j ∈ B, hV.eigenvalues j < t) :
    A.card + B.card ≤ d + (U - V).rank := by
  by_contra hcon
  push Not at hcon
  have hrk : (U - V).rank ≤ d := by
    have := Matrix.rank_le_card_width (U - V); simpa using this
  set WU := (hU.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  set WV := (hV.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hWU : star WU * WU = 1 := Unitary.star_mul_self_of_mem (hU.eigenvectorUnitary).2
  have hWV : star WV * WV = 1 := Unitary.star_mul_self_of_mem (hV.eigenvectorUnitary).2
  obtain ⟨x, hx0, hxS, hxT, hxK⟩ := dim_lemma (LinearMap.range (psi WU A))
    (LinearMap.range (psi WV B)) (LinearMap.ker (U - V).mulVecLin) (by
      rw [psi_finrank hWU, psi_finrank hWV, ker_finrank]; omega)
  obtain ⟨c, rfl⟩ := hxS
  obtain ⟨c', hc'⟩ := hxT
  have hUV : U *ᵥ psi WU A c = V *ᵥ psi WU A c := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, sub_mulVec, sub_eq_zero] at hxK; exact hxK
  obtain ⟨qU, nU⟩ := quad_sub hU A c
  obtain ⟨qV, nV⟩ := quad_sub hV B c'
  rw [hc'] at qV nV
  -- upper bound
  have h1 : t * (star (psi WU A c) ⬝ᵥ psi WU A c).re ≤ (star (psi WU A c) ⬝ᵥ (U *ᵥ psi WU A c)).re := by
    rw [qU, nU, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : i ∈ A
    · exact mul_le_mul_of_nonneg_right (hA i hi) (sq_nonneg _)
    · simp [ext, hi]
  -- strict lower bound
  have hne : ∃ j ∈ B, ext B c' j ≠ 0 := by
    by_contra hall; push Not at hall
    apply hx0
    rw [← hc']
    show WV *ᵥ ext B c' = 0
    have : ext B c' = 0 := by
      funext j; by_cases hj : j ∈ B
      · exact hall j hj
      · simp [ext, hj]
    rw [this, mulVec_zero]
  have h2 : (star (psi WU A c) ⬝ᵥ (V *ᵥ psi WU A c)).re < t * (star (psi WU A c) ⬝ᵥ psi WU A c).re := by
    rw [qV, nV, Finset.mul_sum]
    obtain ⟨j, hjB, hj0⟩ := hne
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i ∈ B
      · exact mul_le_mul_of_nonneg_right (hB i hi).le (sq_nonneg _)
      · simp [ext, hi]
    · exact ⟨j, Finset.mem_univ j, mul_lt_mul_of_pos_right (hB j hjB) (by positivity)⟩
  rw [hUV] at h1
  linarith


end MatrixSpectralAux

theorem solution {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℂ)
    (hU : U.IsHermitian) (hV : V.IsHermitian) (t : ℝ) :
    (Finset.univ.filter (fun i => hU.eigenvalues i ≤ t)).card ≤
        (Finset.univ.filter (fun i => hV.eigenvalues i ≤ t)).card + (U - V).rank ∧
    (Finset.univ.filter (fun i => t ≤ hU.eigenvalues i)).card ≤
        (Finset.univ.filter (fun i => t ≤ hV.eigenvalues i)).card + (U - V).rank := by
  constructor
  · have h := MatrixSpectralAux.main_le hU hV (Finset.univ.filter (fun i => hU.eigenvalues i ≤ t))
      (Finset.univ.filter (fun j => t < hV.eigenvalues j)) t
      (fun i hi => (Finset.mem_filter.mp hi).2) (fun j hj => (Finset.mem_filter.mp hj).2)
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j => hV.eigenvalues j ≤ t)
    simp only [not_le, Finset.card_univ, Fintype.card_fin] at hc
    omega
  · have h := MatrixSpectralAux.main_ge hU hV (Finset.univ.filter (fun i => t ≤ hU.eigenvalues i))
      (Finset.univ.filter (fun j => hV.eigenvalues j < t)) t
      (fun i hi => (Finset.mem_filter.mp hi).2) (fun j hj => (Finset.mem_filter.mp hj).2)
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun j => t ≤ hV.eigenvalues j)
    simp only [not_le, Finset.card_univ, Fintype.card_fin] at hc
    omega


