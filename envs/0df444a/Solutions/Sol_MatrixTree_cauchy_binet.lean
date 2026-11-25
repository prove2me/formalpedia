-- Prove2me | solution 1 for MatrixTree.cauchy_binet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:14:03.461901+00:00
-- url     : https://prove2.me/submissions/b6ce429f-ae7a-4070-b2d7-e32a315ca8fa

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_det_mul_eq_sum_fun
public import Theorems.Thm_MatrixTree_det_submatrix_eq_zero_of_not_injective
public import Theorems.Thm_MatrixTree_sum_perm_eq_det

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset (Fin k) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  set F : (Fin m → Fin k) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  rw [det_mul_eq_sum_fun]
  have h1 : ∑ p : Fin m → Fin k, F p = ∑ p ∈ univ.filter Function.Injective, F p := by
    refine (Finset.sum_subset (filter_subset _ _) fun p _ hp => ?_).symm
    simp only [mem_filter, mem_univ, true_and] at hp
    simp [hF, det_submatrix_eq_zero_of_not_injective A p hp]
  have h2 : ∑ p ∈ univ.filter Function.Injective, F p =
      ∑ p : {p : Fin m → Fin k // Function.Injective p}, F p.1 :=
    Finset.sum_subtype _ (by simp) F
  let g : (Σ _ : {S : Finset (Fin k) // S.card = m}, Equiv.Perm (Fin m)) →
      {p : Fin m → Fin k // Function.Injective p} := fun x =>
    ⟨x.1.1.orderEmbOfFin x.1.2 ∘ x.2, (x.1.1.orderEmbOfFin x.1.2).injective.comp x.2.injective⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨S, hS⟩, τ⟩ ⟨⟨S', hS'⟩, τ'⟩ h
      simp only [g, Subtype.mk.injEq] at h
      have hSS : S = S' := by
        have := congrArg Set.range h
        rw [Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Equiv.range_eq_univ,
          Set.image_univ, Set.image_univ, range_orderEmbOfFin, range_orderEmbOfFin] at this
        exact_mod_cast this
      subst hSS
      have : τ = τ' := by
        ext i
        have := congrFun h i
        simp only [Function.comp_apply] at this
        exact congrArg Fin.val ((S.orderEmbOfFin hS).injective this)
      subst this
      rfl
    · rintro ⟨p, hp⟩
      have hc : (univ.image p).card = m := by
        rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
      have hmem : ∀ i, p i ∈ univ.image p := fun i => mem_image_of_mem p (mem_univ i)
      let t : Fin m → Fin m := fun i => ((univ.image p).orderIsoOfFin hc).symm ⟨p i, hmem i⟩
      have ht : ∀ i, (univ.image p).orderEmbOfFin hc (t i) = p i := by
        intro i
        rw [← coe_orderIsoOfFin_apply]
        simp [t]
      have htinj : Function.Injective t := by
        intro i j hij
        apply hp
        rw [← ht i, ← ht j, hij]
      refine ⟨⟨⟨univ.image p, hc⟩, Equiv.ofBijective t (Finite.injective_iff_bijective.mp htinj)⟩,
        ?_⟩
      ext i
      simp [g, ht]
  rw [h1, h2, ← hg.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact sum_perm_eq_det A B (S.1.orderEmbOfFin S.2)
end MatrixTree
