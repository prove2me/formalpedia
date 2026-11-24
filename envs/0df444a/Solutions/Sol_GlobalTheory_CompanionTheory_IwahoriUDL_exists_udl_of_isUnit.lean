-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.exists_udl_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:57:44.189172+00:00
-- url     : https://prove2.me/submissions/14d04179-cf6a-44a9-8bd9-083e5f91de14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_ex_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_ex_inr
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_up_step
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_lo_step
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_di_step
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_fromBlocks_udl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.IwahoriUDL
theorem _root_.solution (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x)) (n : ℕ) :
    ∀ g : Matrix (Fin n) (Fin n) R,
      (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) →
        ∃ u d l : Matrix (Fin n) (Fin n) R, IsUp I u ∧ IsDi I d ∧ IsLo I l ∧ g = u * d * l := by
  induction n with
  | zero =>
    intro g _
    exact ⟨1, 1, 1, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      ⟨fun i => i.elim0, fun i => i.elim0⟩, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro g hg
    set A : Matrix (Fin n) (Fin n) R := fun i j => g i.castSucc j.castSucc with hA
    set c : Matrix (Fin n) (Fin 1) R := fun i _ => g i.castSucc (Fin.last n) with hc
    set r : Matrix (Fin 1) (Fin n) R := fun _ j => g (Fin.last n) j.castSucc with hr
    set s : R := g (Fin.last n) (Fin.last n) with hs
    have hs1 : s - 1 ∈ I := by simpa [hs] using hg (Fin.last n) (Fin.last n)
    have hsu : IsUnit s := by simpa using hI _ hs1
    obtain ⟨t, hst⟩ := hsu.exists_right_inv
    have hts : t * s = 1 := by rw [mul_comm]; exact hst
    have hcI : ∀ i k, c i k ∈ I := fun i k => by
      have := hg i.castSucc (Fin.last n)
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero] at this
      exact this
    have hrI : ∀ k j, r k j ∈ I := fun k j => by
      have := hg (Fin.last n) j.castSucc
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero] at this
      exact this
    set a : Matrix (Fin 1) (Fin 1) R := fun _ _ => s with ha
    set b : Matrix (Fin 1) (Fin 1) R := fun _ _ => t with hb
    have hab : a * b = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hst
    have hba : b * a = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hts
    have hS : ∀ i j, (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
      intro i j
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
        have := hg i.castSucc j.castSucc
        simpa [hA, Matrix.one_apply] using this
      have h2 : (c * b * r) i j ∈ I := by
        simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
        exact I.mul_mem_right _ (I.mul_mem_right _ (hcI i default))
      have h3 : (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j =
          (A i j - (1 : Matrix (Fin n) (Fin n) R) i j) - (c * b * r) i j := by
        simp only [Matrix.sub_apply]
        ring
      rw [h3]
      exact I.sub_mem h1 h2
    obtain ⟨u, d, l, hu, hd, hl, hudl⟩ := ih _ hS
    have hcb : ∀ i k, (c * b) i k ∈ I := fun i k => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_right _ (hcI i default)
    have hbr : ∀ k j, (b * r) k j ∈ I := fun k j => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_left _ (hrI default j)
    have haI : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I := fun k k' => by
      simpa [ha, Matrix.one_apply, Subsingleton.elim k k'] using hs1
    refine ⟨_, _, _, up_step hu hcb, di_step hd haI, lo_step hl hbr, ?_⟩
    have hblock : g.submatrix (ex n) (ex n) = fromBlocks A c r a := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rw [submatrix_apply, ex_inl, ex_inl]; rfl
      · rw [submatrix_apply, ex_inl, ex_inr]; rfl
      · rw [submatrix_apply, ex_inr, ex_inl]; rfl
      · rw [submatrix_apply, ex_inr, ex_inr]; rfl
    have hg' : g = (fromBlocks A c r a).submatrix (ex n).symm (ex n).symm := by
      rw [← hblock]
      simp
    rw [hg', fromBlocks_udl A c r a b hab hba u d l hudl]
    simp only [Matrix.submatrix_mul_equiv]
end GlobalTheory.CompanionTheory.IwahoriUDL
