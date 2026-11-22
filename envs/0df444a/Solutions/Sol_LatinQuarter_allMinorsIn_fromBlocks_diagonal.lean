-- Prove2me | solution 1 for LatinQuarter.allMinorsIn_fromBlocks_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:15.303744+00:00
-- url     : https://prove2.me/submissions/0b32b9d4-bff5-43c0-90dd-5c08d76e3d48

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Theorems.Thm_LatinQuarter_det_mem_pow_of_rows

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution {k h t : ℕ}
    (A : Matrix (Fin k) (Fin k) R) (Z : Matrix (Fin h) (Fin h) R)
    (J : Ideal R) (hZ : ∀ i j, Z i j ∈ J) :
    AllMinorsIn (Matrix.fromBlocks A 0 0 Z) t (J ^ (t - k)) := by
  classical
  intro r c
  by_cases hr : Function.Injective r
  · let s : Finset (Fin t) := Finset.univ.filter (fun i => (r i).isRight)
    have htop : sᶜ.card ≤ k := by
      have hsub : sᶜ.image r ⊆
          Finset.univ.map (Function.Embedding.inl : Fin k ↪ Fin k ⊕ Fin h) := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        cases he : r i with
        | inl a => simp
        | inr b => simp [s, he] at hi
      have hc := Finset.card_le_card hsub
      simpa [Finset.card_image_of_injective _ hr] using hc
    have hs : t - k ≤ s.card := by
      have hc := Finset.card_add_card_compl s
      simp only [Fintype.card_fin] at hc
      omega
    apply Ideal.pow_le_pow_right hs
    apply det_mem_pow_of_rows _ J s
    intro i hi j
    have hir : (r i).isRight := (Finset.mem_filter.mp hi).2
    cases he : r i with
    | inl a => simp [he] at hir
    | inr b =>
      cases hc : c j with
      | inl a => simp [Matrix.submatrix, he, hc]
      | inr d => simpa [Matrix.submatrix, he, hc] using hZ b d
  · simp only [Function.Injective, not_forall] at hr
    obtain ⟨a, b, hab⟩ := hr
    have he : r a = r b := by tauto
    have hn : a ≠ b := by tauto
    rw [Matrix.det_zero_of_row_eq hn (by ext j; simp [Matrix.submatrix, he])]
    exact Ideal.zero_mem _
end LatinQuarter
