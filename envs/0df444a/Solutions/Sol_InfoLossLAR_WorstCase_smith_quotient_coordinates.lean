-- Prove2me | solution 1 for InfoLossLAR.WorstCase.smith_quotient_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:42:23.347197+00:00
-- url     : https://prove2.me/submissions/e6cda3ad-0ffc-44e5-b7a2-fe56a689d6b5

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
set_option autoImplicit false
namespace InfoLossLAR.WorstCase

private def tailIndex {r d : ℕ} (h : r ≤ d) (j : Fin (d-r)) : Fin d := ⟨r+j.val, by omega⟩

private lemma emb_mulVec (r d : ℕ) (hr : r ≤ d) (y : Fin d → ℤ) (j : Fin (d-r)) :
    ((embE r d).transpose.mulVec y) j = y (tailIndex hr j) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, embE]
  have heq (i : Fin d) : (i.val = r + j.val) ↔ i = tailIndex hr j := by
    constructor
    · intro hi; apply Fin.ext; simpa [tailIndex] using hi
    · intro hi; subst i; rfl
  simp only [heq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma coord (q r d : ℕ) (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) (z : Fin d → ℤ) (j : Fin (d-r)) :
    (S.P.mulVec z) j = S.U.mulVec z (tailIndex S.r_le j) := by
  simp only [SmithData.P, ← Matrix.mulVec_mulVec]
  exact emb_mulVec r d S.r_le _ _
private lemma coord_surjective (q r d : ℕ) [Fact q.Prime] (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) :
    Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) := by
  classical
  intro x
  let y : Fin d → ℤ := fun i => if hi : r ≤ i.val then ((x ⟨i.val-r, by omega⟩).val : ℤ) else 0
  refine ⟨S.U⁻¹.mulVec y, ?_⟩
  funext j
  simp only [modq, coord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S.U S.U_unimod,
    Matrix.one_mulVec]
  change ((y (tailIndex S.r_le j) : ℤ) : ZMod q) = x j
  have ht : r ≤ (tailIndex S.r_le j).val := by simp [tailIndex]
  simp only [y, dif_pos ht]
  have hj : (⟨(tailIndex S.r_le j).val-r, by omega⟩ : Fin (d-r)) = j := by
    apply Fin.ext; simp [tailIndex]
  rw [hj]
  simpa using ZMod.natCast_zmod_val (x j)
private lemma image_smith (q r d : ℕ) (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) (z : Fin d → ℤ) :
    z ∈ imageLattice T ↔ S.U.mulVec z ∈ imageLattice (smithDiag q r d) := by
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hz
    change T.mulVec w = z at hw
    refine ⟨S.V⁻¹.mulVec w, ?_⟩
    change (smithDiag q r d).mulVec (S.V⁻¹.mulVec w) = S.U.mulVec z
    rw [← S.smith, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hv : S.V.mulVec (S.V⁻¹.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S.V S.V_unimod, Matrix.one_mulVec]
    rw [hv, hw]
  · intro hz
    obtain ⟨w, hw⟩ := hz
    change (smithDiag q r d).mulVec w = S.U.mulVec z at hw
    refine ⟨S.V.mulVec w, ?_⟩
    change T.mulVec (S.V.mulVec w) = z
    rw [← S.smith, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hw
    have hh := congrArg (S.U⁻¹.mulVec) hw
    have hi (x : Fin d → ℤ) : S.U⁻¹.mulVec (S.U.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S.U S.U_unimod, Matrix.one_mulVec]
    rw [hi, hi] at hh
    exact hh

private lemma image_diag_iff (q r d : ℕ) (hr : r ≤ d) (y : Fin d → ℤ) :
    y ∈ imageLattice (smithDiag q r d) ↔
      ∀ j : Fin (d-r), (q : ℤ) ∣ y (tailIndex hr j) := by
  classical
  constructor
  · intro hy j
    obtain ⟨w, hw⟩ := hy
    change (smithDiag q r d).mulVec w = y at hw
    have hh := congrFun hw (tailIndex hr j)
    have ht : ¬ (tailIndex hr j).val < r := by simp [tailIndex]
    simp only [smithDiag, Matrix.mulVec_diagonal, ht, ite_false] at hh
    exact ⟨w (tailIndex hr j), hh.symm⟩
  · intro hy
    have ht (i : Fin d) (hi : ¬ i.val < r) : (q : ℤ) ∣ y i := by
      have hr' : r ≤ i.val := by omega
      let j : Fin (d-r) := ⟨i.val-r, by omega⟩
      have hh : tailIndex hr j = i := by apply Fin.ext; simp [tailIndex, j]; omega
      simpa [hh] using hy j
    let w : Fin d → ℤ := fun i => if i.val < r then y i else y i / (q : ℤ)
    refine ⟨w, ?_⟩
    change (smithDiag q r d).mulVec w = y
    funext i
    simp only [smithDiag, Matrix.mulVec_diagonal]
    split_ifs with hi
    · simp [w, hi]
    · simp only [w, hi, ite_false]
      exact Int.mul_ediv_cancel' (ht i hi)

private lemma coord_kernel (q r d : ℕ) [Fact q.Prime] (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) (z : Fin d → ℤ) :
    modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T := by
  rw [image_smith, image_diag_iff q r d S.r_le]
  constructor
  · intro h j
    have hh := congrFun h j
    change ((S.P.mulVec z) j : ZMod q) = 0 at hh
    rw [coord] at hh
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh
  · intro h
    funext j
    change ((S.P.mulVec z) j : ZMod q) = 0
    rw [coord]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h j)

end InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase

theorem solution (q r d : ℕ) [Fact q.Prime]
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
    Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) ∧
    (∀ z : Fin d → ℤ, modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T) := by
  exact ⟨coord_surjective q r d T S, coord_kernel q r d T S⟩
