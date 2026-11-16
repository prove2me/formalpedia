-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:33:59.244196+00:00
-- url     : https://prove2.me/submissions/4330b0f8-33fa-421d-bee6-9f0c992b14ac

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Theorems.Thm_InfoLossLAR_WorstCase_smith_modular_rank_nullity
import Theorems.Thm_InfoLossLAR_WorstCase_smith_quotient_coordinates
set_option autoImplicit false
open InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase

lemma smithDiag_det (q r d : ℕ) (hr : r ≤ d) :
  (smithDiag q r d).det = (q : ℤ) ^ (d-r) := by
  classical
  have hcard : (Finset.univ.filter (fun i : Fin d => ¬ (i : ℕ) < r)).card = d-r := by
    have h : (Finset.univ : Finset (Fin (d-r))).card =
        (Finset.univ.filter (fun i : Fin d => ¬ (i : ℕ) < r)).card := by
      apply Finset.card_bij (fun i _ => ⟨r + i.val, by omega⟩)
      · intro i hi; simp
      · intro a ha b hb heq; apply Fin.ext; have h := congrArg Fin.val heq; simp only at h; omega
      · intro b hb
        have hb' : ¬ b.val < r := (Finset.mem_filter.mp hb).2
        refine ⟨⟨b.val-r, by omega⟩, Finset.mem_univ _, ?_⟩
        apply Fin.ext
        simp only
        omega
    simpa using h.symm
  simp only [smithDiag, Matrix.det_diagonal]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const, hcard]

theorem rounding_matrix_abs_det
    (q r d : ℕ) (T : Matrix (Fin d) (Fin d) ℤ)
    (S : SmithData q r d T) :
    |T.det| = (q : ℤ) ^ (d - r) := by
  have hu : |S.U.det| = 1 := Int.isUnit_iff_abs_eq.mp S.U_unimod
  have hv : |S.V.det| = 1 := Int.isUnit_iff_abs_eq.mp S.V_unimod
  have h := congrArg Matrix.det S.smith
  rw [Matrix.det_mul, Matrix.det_mul, smithDiag_det q r d S.r_le] at h
  have ha := congrArg abs h
  rw [abs_mul, abs_mul, hu, hv] at ha
  simpa using ha
end InfoLossLAR.WorstCase


theorem solution (q r d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hd : 1 ≤ d) (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
 (matModq q T).rank = r ∧ Module.finrank (ZMod q) (LinearMap.ker (Matrix.mulVecLin (matModq q T))) = d - r ∧ |T.det| = (q : ℤ) ^ (d - r) ∧ (∀ z : Fin d → ℤ, (q : ℤ) • z ∈ imageLattice T) ∧ Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) ∧ (∀ z : Fin d → ℤ, modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T) ∧ Nat.card ((Fin d → ℤ) ⧸ imageLattice T) = q ^ (d - r) ∧ (Nontrivial ((Fin d → ℤ) ⧸ imageLattice T) ↔ 1 ≤ d - r) := by
  classical
  have hmod := InfoLossLAR.WorstCase.smith_modular_rank_nullity q r d T S
  have hdet := InfoLossLAR.WorstCase.rounding_matrix_abs_det q r d T S
  have hcoord := InfoLossLAR.WorstCase.smith_quotient_coordinates q r d T S
  have hsurj := hcoord.1
  have hker := hcoord.2
  let f : (Fin d → ℤ) →ₗ[ℤ] (Fin (d-r) → ZMod q) := (AddMonoidHom.toIntLinearMap {
    toFun := fun z => modq q (S.P.mulVec z)
    map_zero' := by ext i; simp [modq, Matrix.mulVec]
    map_add' := by intro a b; ext i; simp [modq, Matrix.mulVec, Finset.sum_add_distrib, mul_add] })
  have hf (z : Fin d → ℤ) : f z = modq q (S.P.mulVec z) := rfl
  have hk : f.ker = imageLattice T := by
    ext z
    exact hker z
  have he : ((Fin d → ℤ) ⧸ imageLattice T) ≃ₗ[ℤ] (Fin (d-r) → ZMod q) :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hsurj)
  have hqz (z : Fin d → ℤ) : (q : ℤ) • z ∈ imageLattice T := by
    apply (hker _).mp
    change f ((q : ℤ) • z) = 0
    rw [map_smul]
    ext i
    simp
  have hc : Nat.card ((Fin d → ℤ) ⧸ imageLattice T) = q ^ (d-r) := by
    rw [Nat.card_congr he.toEquiv, Nat.card_pi]
    simp [Nat.card_zmod]
  have hn : Nontrivial ((Fin d → ℤ) ⧸ imageLattice T) ↔ 1 ≤ d-r := by
    constructor
    · intro hn
      by_contra hn0
      have h0 : d-r = 0 := by omega
      have hc1 : Nat.card ((Fin d → ℤ) ⧸ imageLattice T) = 1 := by simpa [h0] using hc
      exact (not_subsingleton_iff_nontrivial.mpr hn) (Nat.card_eq_one_iff_unique.mp hc1).1
    · intro hp
      apply not_subsingleton_iff_nontrivial.mp
      intro hsub
      have hc1 : Nat.card ((Fin d → ℤ) ⧸ imageLattice T) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
      rw [hc] at hc1
      have hh := Nat.one_lt_pow (a := q) (n := d-r) (by omega) (Fact.out : q.Prime).one_lt
      omega
  exact ⟨hmod.1, hmod.2, hdet, hqz, hsurj, hker, hc, hn⟩
