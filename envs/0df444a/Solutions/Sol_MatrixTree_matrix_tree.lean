-- Prove2me | solution 1 for MatrixTree.matrix_tree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:43:03.816486+00:00
-- url     : https://prove2.me/submissions/9863119a-e26c-47b9-ac79-27de84879ec5

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_cauchy_binet
public import Theorems.Thm_MatrixTree_card_ne_add_one
public import Theorems.Thm_MatrixTree_det_incMat_sq_of_isTree
public import Theorems.Thm_MatrixTree_det_incMat_eq_zero_of_not_isTree
public import Theorems.Thm_MatrixTree_lapMatrix_eq_sum

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (Nat.card {H : SimpleGraph V // H ≤ G ∧ H.IsTree} : ℤ) =
      ((G.lapMatrix ℤ).submatrix (Subtype.val : {u // u ≠ v} → V) Subtype.val).det := by
  classical
  set m := Fintype.card {u // u ≠ v} with hm
  let φ : Fin m ≃ {u // u ≠ v} := (Fintype.equivFin _).symm
  let ψ : Fin (Fintype.card G.edgeSet) ≃ G.edgeSet := (Fintype.equivFin _).symm
  let E : Finset (Fin (Fintype.card G.edgeSet)) → Set (Sym2 V) :=
    fun T => (fun j => (ψ j : Sym2 V)) '' T
  have hψinj : Function.Injective (fun j => (ψ j : Sym2 V)) :=
    Subtype.val_injective.comp ψ.injective
  have hE : ∀ T, (fromEdgeSet (E T)).edgeSet = E T := by
    intro T
    rw [edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_)
    rintro _ ⟨j, _, rfl⟩
    exact G.not_isDiag_of_mem_edgeSet (ψ j).2
  let A : Matrix (Fin m) (Fin (Fintype.card G.edgeSet)) ℤ :=
    Matrix.of fun i j => inc (ψ j : Sym2 V) (φ i)
  have hAA : ((G.lapMatrix ℤ).submatrix (Subtype.val : {u // u ≠ v} → V) Subtype.val).submatrix
      φ φ = A * Aᵀ := by
    ext i j
    simp only [submatrix_apply, mul_apply, transpose_apply, A, of_apply, lapMatrix_eq_sum]
    rw [Finset.sum_subtype G.edgeFinset (p := (· ∈ G.edgeSet)) (by simp)]
    exact (Equiv.sum_comp ψ
      (fun e : G.edgeSet => inc (e : Sym2 V) (φ i) * inc (e : Sym2 V) (φ j))).symm
  have hterm : ∀ S : {S : Finset (Fin (Fintype.card G.edgeSet)) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det * (Aᵀ.submatrix (S.1.orderEmbOfFin S.2) id).det
        = if (fromEdgeSet (E S.1)).IsTree then 1 else 0 := by
    intro S
    set g : {u // u ≠ v} → Sym2 V := fun w => (ψ (S.1.orderEmbOfFin S.2 (φ.symm w)) : Sym2 V)
      with hg_def
    have hg : ∀ w, ¬ (g w).IsDiag := fun w => G.not_isDiag_of_mem_edgeSet (ψ _).2
    have hrange : Set.range g = E S.1 := by
      ext e
      simp only [g, E, Set.mem_range, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨_, S.1.orderEmbOfFin_mem S.2 _, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have : j ∈ Set.range (S.1.orderEmbOfFin S.2) := by
          rw [range_orderEmbOfFin]; exact hj
        obtain ⟨i, rfl⟩ := this
        exact ⟨φ i, by simp⟩
    have hsub : A.submatrix id (S.1.orderEmbOfFin S.2) = (incMat v g).submatrix φ φ := by
      ext i j
      simp [A, incMat, g]
    rw [← transpose_submatrix, det_transpose, hsub, det_submatrix_equiv_self, ← hrange]
    split_ifs with hT
    · rw [← sq]; exact det_incMat_sq_of_isTree v g hg hT
    · rw [det_incMat_eq_zero_of_not_isTree v g hg hT, zero_mul]
  rw [← det_submatrix_equiv_self φ, hAA, cauchy_binet, Finset.sum_congr rfl fun S _ => hterm S,
    Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_eq_of_bijective (fun S => ⟨fromEdgeSet (E S.1.1), ?_, S.2⟩) ⟨?_, ?_⟩
  · intro a b hab
    rw [fromEdgeSet_adj] at hab
    obtain ⟨⟨j, _, hj⟩, _⟩ := hab
    rw [← mem_edgeSet, ← hj]
    exact (ψ j).2
  · intro S S' h
    have h1 := congrArg (fun H : {H : SimpleGraph V // H ≤ G ∧ H.IsTree} => H.1.edgeSet) h
    simp only [hE] at h1
    have h2 : (S.1.1 : Set _) = S'.1.1 := Set.image_injective.mpr hψinj h1
    exact Subtype.ext (Subtype.ext (Finset.coe_inj.mp h2))
  · rintro ⟨H, hle, hT⟩
    let T := univ.filter (fun j => (ψ j : Sym2 V) ∈ H.edgeSet)
    have hET : E T = H.edgeSet := by
      ext e
      simp only [E, T, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro he
        refine ⟨ψ.symm ⟨e, edgeSet_mono hle he⟩, ?_, ?_⟩ <;> simp [he]
    have hcard : T.card = m := by
      have h1 := Nat.card_image_of_injective hψinj (T : Set _)
      have h2 := (isTree_iff_connected_and_card.mp hT).2
      have h3 := card_ne_add_one v
      change Nat.card (E T) = _ at h1
      rw [hET] at h1
      rw [Nat.card_eq_fintype_card (α := {u // u ≠ v})] at h3
      simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h1 h2
      omega
    refine ⟨⟨⟨T, hcard⟩, ?_⟩, ?_⟩
    · change (fromEdgeSet (E T)).IsTree
      rw [hET, fromEdgeSet_edgeSet]; exact hT
    · apply Subtype.ext
      change fromEdgeSet (E T) = H
      rw [hET, fromEdgeSet_edgeSet]
end MatrixTree
