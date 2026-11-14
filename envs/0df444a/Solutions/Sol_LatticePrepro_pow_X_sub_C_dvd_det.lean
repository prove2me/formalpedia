-- Prove2me | solution 1 for LatticePrepro.pow_X_sub_C_dvd_det
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:56.120092+00:00
-- url     : https://prove2.me/submissions/d09a88d7-e538-4a11-9c07-690e7a2dab4a

import Mathlib


namespace LatticePrepro

open Polynomial Matrix

section ZeroRows

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix of rank `b` can be multiplied on the left by an invertible matrix so that
`|n| - b` of its rows vanish. -/
theorem exists_isUnit_mul_rows_eq_zero (B : Matrix n n K) :
    ∃ (U : Matrix n n K) (ι : Fin (Fintype.card n - B.rank) → n),
      IsUnit U.det ∧ Function.Injective ι ∧ ∀ k j, (U * B) (ι k) j = 0 := by
  obtain ⟨V, W, e, hV, hW, hVBW⟩ := Matrix.exists_rank_normal_form B
  refine ⟨V, fun k => e.symm (Sum.inr k), (Matrix.isUnit_iff_isUnit_det _).mp hV,
    fun a b hab => Sum.inr_injective (e.symm.injective hab), fun k j => ?_⟩
  have hWdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).mp hW
  have hVB : V * B = (fromBlocks 1 0 0 0).submatrix e e * W⁻¹ := by
    calc V * B = V * B * W * W⁻¹ := (Matrix.mul_nonsing_inv_cancel_right W (V * B) hWdet).symm
      _ = (fromBlocks 1 0 0 0).submatrix e e * W⁻¹ := by rw [hVBW]
  rw [hVB, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  rcases hx : e x with a | a
  · simp [Matrix.fromBlocks_apply₂₁]
  · simp [Matrix.fromBlocks_apply₂₂]

end ZeroRows

section Dvd

variable {𝕊 : Type*} [Field 𝕊] {n : Type*} [Fintype n] [DecidableEq n]

/-- For a square polynomial matrix `M` and a point `s`, `(X - s)^{|n| - rank M(s)}` divides
`det M`. -/
private theorem pow_X_sub_C_dvd_det (M : Matrix n n 𝕊[X]) (s : 𝕊) :
    (X - C s) ^ (Fintype.card n - (M.map (eval s)).rank) ∣ M.det := by
  classical
  set B := M.map (eval s) with hB
  obtain ⟨U, ι, hU, hι, hrows⟩ := exists_isUnit_mul_rows_eq_zero B
  set U' : Matrix n n 𝕊[X] := U.map C with hU'
  have hmap : (U' * M).map (eval s) = U * B := by
    have h1 := Matrix.map_mul (L := U') (M := M) (f := Polynomial.evalRingHom s)
    simp only [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [U', Matrix.map_apply]
  have hdvd : ∀ i j, i ∈ Finset.univ.image ι → ∃ q, (U' * M) i j = (X - C s) * q := by
    intro i j hi
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi
    have hroot : X - C s ∣ (U' * M) (ι k) j := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      have := congrFun (congrFun hmap (ι k)) j
      simp only [Matrix.map_apply] at this
      rw [this]; exact hrows k j
    exact hroot
  choose! Q hQ using hdvd
  set Z : Finset n := Finset.univ.image ι with hZ
  let w : n → 𝕊[X] := fun i => if i ∈ Z then X - C s else 1
  let A' : Matrix n n 𝕊[X] := Matrix.of fun i j => if i ∈ Z then Q i j else (U' * M) i j
  have hfactor : U' * M = Matrix.of fun i j => w i * A' i j := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, w, A']
    split_ifs with hi
    · exact hQ i j hi
    · rw [one_mul]
  have hprod : ∏ i, w i = (X - C s) ^ (Fintype.card n - B.rank) := by
    simp only [w]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.card_image_of_injective _ hι, Finset.card_univ, Fintype.card_fin]
  have hdet : (U' * M).det = (X - C s) ^ (Fintype.card n - B.rank) * A'.det := by
    rw [hfactor, Matrix.det_mul_column, hprod]
  have hdvd' : (X - C s) ^ (Fintype.card n - B.rank) ∣ (U' * M).det := ⟨A'.det, hdet⟩
  rw [Matrix.det_mul] at hdvd'
  have hU'det : IsUnit U'.det := by
    rw [hU', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Polynomial.isUnit_C.mpr hU
  exact (hU'det.dvd_mul_left).mp hdvd'

end Dvd

end LatticePrepro

open Polynomial Matrix
variable {𝕊 : Type*} [Field 𝕊] {n : Type*} [Fintype n] [DecidableEq n]
theorem solution (M : Matrix n n 𝕊[X]) (s : 𝕊) :
    (X - C s) ^ (Fintype.card n - (M.map (eval s)).rank) ∣ M.det :=
  @LatticePrepro.pow_X_sub_C_dvd_det 𝕊 _ n _ _ M s
