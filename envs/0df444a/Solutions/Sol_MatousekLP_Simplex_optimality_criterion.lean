-- Prove2me | solution 1 for MatousekLP.Simplex.optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:33:27.425711+00:00
-- url     : https://prove2.me/submissions/ac71ee37-9218-41ae-89cf-532b4d40e1b6

import Definitions.Def_MatousekLP_Simplex_Tableau
import Mathlib

namespace TabCore

open Matrix MatousekLP.Simplex Finset

variable {m n : ℕ}

lemma sum_split (B : Finset (Fin n)) (hB : B.card = m) (f : Fin n → ℝ) :
    ∑ j, f j = ∑ i, f (kIdx B hB i) + ∑ j, f (lIdx B hB j) := by
  rw [← Finset.sum_add_sum_compl B f]
  congr 1
  · conv_lhs => rw [← image_orderEmbOfFin_univ B hB]
    rw [Finset.sum_image (fun a _ b _ h => (B.orderEmbOfFin hB).injective h)]; rfl
  · conv_lhs => rw [← image_orderEmbOfFin_univ Bᶜ (card_compl_eq hB)]
    rw [Finset.sum_image (fun a _ b _ h => (Bᶜ.orderEmbOfFin (card_compl_eq hB)).injective h)]; rfl

lemma kIdx_mem (B : Finset (Fin n)) (hB : B.card = m) (i : Fin m) : kIdx B hB i ∈ B :=
  orderEmbOfFin_mem _ _ _

lemma lIdx_notMem (B : Finset (Fin n)) (hB : B.card = m) (j : Fin (n - m)) : lIdx B hB j ∉ B :=
  Finset.mem_compl.mp (orderEmbOfFin_mem _ _ _)

lemma mulVec_split (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) (hB : B.card = m)
    (x : Fin n → ℝ) :
    A *ᵥ x = basisMatrix A B hB *ᵥ (fun i => x (kIdx B hB i)) +
      nonbasisMatrix A B hB *ᵥ (fun j => x (lIdx B hB j)) := by
  funext r
  simp only [mulVec, dotProduct, Pi.add_apply, basisMatrix, nonbasisMatrix, submatrix_apply, id]
  exact sum_split B hB (fun j => A r j * x j)

lemma dot_split (c x : Fin n → ℝ) (B : Finset (Fin n)) (hB : B.card = m) :
    c ⬝ᵥ x = (fun i => c (kIdx B hB i)) ⬝ᵥ (fun i => x (kIdx B hB i)) +
      (fun j => c (lIdx B hB j)) ⬝ᵥ (fun j => x (lIdx B hB j)) :=
  sum_split B hB (fun j => c j * x j)

lemma exists_of_parts (B : Finset (Fin n)) (hB : B.card = m) (u : Fin m → ℝ)
    (w : Fin (n - m) → ℝ) :
    ∃ x : Fin n → ℝ, (fun i => x (kIdx B hB i)) = u ∧ (fun j => x (lIdx B hB j)) = w := by
  classical
  refine ⟨fun j => if h : j ∈ B then u ((B.orderIsoOfFin hB).symm ⟨j, h⟩)
    else w ((Bᶜ.orderIsoOfFin (card_compl_eq hB)).symm ⟨j, Finset.mem_compl.mpr h⟩), ?_, ?_⟩
  · funext i
    simp only [dif_pos (kIdx_mem B hB i)]
    congr 1
    exact (B.orderIsoOfFin hB).symm_apply_eq.mpr (Subtype.ext rfl)
  · funext j
    simp only [dif_neg (lIdx_notMem B hB j)]
    congr 1
    exact (Bᶜ.orderIsoOfFin (card_compl_eq hB)).symm_apply_eq.mpr (Subtype.ext rfl)

/-- The standard tableau of a basis with invertible basis matrix. -/
theorem tableau_std (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B : Finset (Fin n)) (hB : B.card = m) (hdet : IsUnit (basisMatrix A B hB).det) :
    IsSimplexTableau A b c B hB (tableauP A b B hB) (tableauQ A B hB) (tableauZ0 A b c B hB)
      (tableauR A c B hB) := by
  intro x z
  set AB := basisMatrix A B hB
  set AN := nonbasisMatrix A B hB
  set xB : Fin m → ℝ := fun i => x (kIdx B hB i)
  set xN : Fin (n - m) → ℝ := fun j => x (lIdx B hB j)
  set cB : Fin m → ℝ := fun i => c (kIdx B hB i)
  set cN : Fin (n - m) → ℝ := fun j => c (lIdx B hB j)
  have hAx : A *ᵥ x = b ↔ xB = tableauP A b B hB + tableauQ A B hB *ᵥ xN := by
    rw [mulVec_split A B hB x]
    unfold tableauP tableauQ
    constructor
    · intro h
      have : xB = AB⁻¹ *ᵥ (b - AN *ᵥ xN) := by
        rw [← h, add_sub_cancel_right, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
      rw [this, mulVec_sub, neg_mulVec, mulVec_mulVec, sub_eq_add_neg]
    · intro h
      show AB *ᵥ xB + AN *ᵥ xN = b
      rw [h, mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, neg_mulVec,
        mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul,
        neg_add_cancel_right]
  have hobj : ∀ v : Fin (n - m) → ℝ,
      cB ⬝ᵥ (tableauP A b B hB + tableauQ A B hB *ᵥ v) + cN ⬝ᵥ v =
        tableauZ0 A b c B hB + tableauR A c B hB ⬝ᵥ v := by
    intro v
    unfold tableauP tableauQ tableauZ0 tableauR
    simp only [dotProduct_add, neg_mulVec, dotProduct_neg, dotProduct_mulVec, sub_dotProduct, cB, cN]
    ring
  constructor
  · rintro ⟨h1, h2⟩
    have hxB := hAx.mp h1
    refine ⟨hxB, ?_⟩
    rw [h2, dot_split c x B hB, ← hobj]
    show cB ⬝ᵥ xB + cN ⬝ᵥ xN = _
    rw [hxB]
  · rintro ⟨h1, h2⟩
    refine ⟨hAx.mpr h1, ?_⟩
    rw [h2, dot_split c x B hB, ← hobj]
    show _ = cB ⬝ᵥ xB + cN ⬝ᵥ xN
    rw [h1]

end TabCore

open Matrix MatousekLP.Simplex TabCore in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n)) (hB : B.card = m)
    (hfeas : IsFeasibleBasisOf A b B hB) (hr : tableauR A c B hB ≤ 0) (x : Fin n → ℝ)
    (hx : IsBasicSolutionFor A b B x) :
    MatousekLP.BFS.IsOptimal A b c x := by
  have hstd := tableau_std A b c B hB hfeas.1
  have hxN : (fun j => x (lIdx B hB j)) = 0 := funext fun j => hx.2 _ (lIdx_notMem B hB j)
  obtain ⟨hxB, hcx⟩ := (hstd x (c ⬝ᵥ x)).mp ⟨hx.1, rfl⟩
  rw [hxN, mulVec_zero, add_zero] at hxB
  rw [hxN, dotProduct_zero, add_zero] at hcx
  have hx0 : 0 ≤ x := by
    intro j
    by_cases hj : j ∈ B
    · have : j ∈ Set.range (kIdx B hB) := by
        unfold kIdx; rw [Finset.range_orderEmbOfFin]; exact hj
      obtain ⟨i, rfl⟩ := this
      have := congrFun hxB i
      rw [show x (kIdx B hB i) = tableauP A b B hB i from this]
      exact hfeas.2 i
    · simp [hx.2 j hj]
  refine ⟨⟨hx.1, hx0⟩, fun y hy => ?_⟩
  obtain ⟨-, hcy⟩ := (hstd y (c ⬝ᵥ y)).mp ⟨hy.1, rfl⟩
  rw [hcy, hcx]
  have : tableauR A c B hB ⬝ᵥ (fun j => y (lIdx B hB j)) ≤ 0 :=
    Finset.sum_nonpos fun j _ => by
      have h1 := hr j; have h2 := hy.2 (lIdx B hB j)
      simp only [Pi.zero_apply] at h1 h2
      nlinarith
  linarith
