-- Prove2me | solution 1 for MatousekLP.Simplex.pivot_step
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T23:48:59.483737+00:00
-- url     : https://prove2.me/submissions/e1f13b53-487d-4975-b3c7-7812c94e2fc2

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


lemma pivot_nonsingular {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Finset (Fin n)) (hB : B.card = m)
    (hdet : IsUnit (basisMatrix A B hB).det) (β : Fin (n - m)) (α : Fin m)
    (hq : tableauQ A B hB α β ≠ 0) (hB' : (pivotBasis B hB β α).card = m) :
    IsUnit (basisMatrix A (pivotBasis B hB β α) hB').det := by
  classical
  let B' := pivotBasis B hB β α
  have hu : kIdx B hB α ∉ B' := by
    simp only [B', pivotBasis, Finset.mem_insert, Finset.mem_erase, not_or]
    exact ⟨fun h => lIdx_notMem B hB β (h ▸ kIdx_mem B hB α), by simp⟩
  have hN : ∀ j, j ≠ β → lIdx B hB j ∉ B' := by
    intro j hj
    simp only [B', pivotBasis, Finset.mem_insert, Finset.mem_erase, not_or]
    refine ⟨?_, fun h => lIdx_notMem B hB j h.2⟩
    exact fun h => hj ((Bᶜ.orderEmbOfFin (card_compl_eq hB)).injective h)
  have hker : ∀ y : Fin m → ℝ, basisMatrix A B' hB' *ᵥ y = 0 → y = 0 := by
    intro y hy
    obtain ⟨x, hxB', hxN'⟩ := exists_of_parts B' hB' y 0
    have hxout : ∀ j, j ∉ B' → x j = 0 := by
      intro j hj
      have hj' : j ∈ Set.range (lIdx B' hB') := by
        unfold lIdx; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hj
      obtain ⟨i, rfl⟩ := hj'
      exact congrFun hxN' i
    have hAx : A *ᵥ x = 0 := by
      rw [mulVec_split A B' hB' x, hxB', hxN', hy, mulVec_zero, add_zero]
    have hxN : (fun j => x (lIdx B hB j)) = Pi.single β (x (lIdx B hB β)) := by
      funext j
      by_cases hj : j = β
      · subst j; simp
      · simp [hj, hxout _ (hN j hj)]
    have hxB := (tableau_std A 0 0 B hB hdet x 0).mp ⟨hAx, by simp⟩
    have hxB0 : (fun i => x (kIdx B hB i)) =
        fun i => tableauQ A B hB i β * x (lIdx B hB β) := by
      funext i
      simpa [tableauP, hxN, mulVec, dotProduct, Pi.single_apply, mul_comm] using congrFun hxB.1 i
    have hxv : x (lIdx B hB β) = 0 := by
      have h := congrFun hxB0 α
      rw [hxout _ hu] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hq
    have hx0 : x = 0 := by
      funext j
      by_cases hj : j ∈ B
      · have hj' : j ∈ Set.range (kIdx B hB) := by
          unfold kIdx; rw [Finset.range_orderEmbOfFin]; exact hj
        obtain ⟨i, rfl⟩ := hj'
        simpa [hxv] using congrFun hxB0 i
      · have hj' : j ∈ Set.range (lIdx B hB) := by
          unfold lIdx; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hj
        obtain ⟨i, rfl⟩ := hj'
        simpa [hxv] using congrFun hxN i
    rw [hx0] at hxB'
    exact hxB'.symm
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have h := hker (u - v) (by rw [mulVec_sub, huv, sub_self])
  exact sub_eq_zero.mp h

end TabCore

open Matrix Filter MatousekLP.Simplex in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (B : Finset (Fin n)) (hB : B.card = m)
    (hfeas : IsFeasibleBasisOf A b B hB) (β : Fin (n - m)) (hr : 0 < tableauR A c B hB β) :
    (∀ α : Fin m, IsEnteringLeaving A b c B hB β α →
        IsFeasibleBasis A b (pivotBasis B hB β α)) ∧
      ((∀ i : Fin m, 0 ≤ tableauQ A B hB i β) →
        IsUnbounded A b c ∧
        ∃ x : ℝ → Fin n → ℝ,
          (∀ t, A *ᵥ x t = b ∧ x t (lIdx B hB β) = t ∧
            ∀ j, j ≠ β → x t (lIdx B hB j) = 0) ∧
          (∀ t, 0 ≤ t → MatousekLP.BFS.IsFeasible A b (x t)) ∧
          Tendsto (fun t => c ⬝ᵥ x t) atTop atTop) := by
  classical
  have hstd := TabCore.tableau_std A b c B hB hfeas.1
  have hparts : ∀ t : ℝ, ∃ x : Fin n → ℝ,
      (fun i => x (kIdx B hB i)) = tableauP A b B hB +
        tableauQ A B hB *ᵥ Pi.single β t ∧
      (fun j => x (lIdx B hB j)) = Pi.single β t := by
    intro t
    exact TabCore.exists_of_parts B hB _ _
  choose x hxB hxN using hparts
  have hAx : ∀ t, A *ᵥ x t = b := by
    intro t
    exact ((hstd (x t) (tableauZ0 A b c B hB + tableauR A c B hB ⬝ᵥ Pi.single β t)).mpr
      ⟨by rw [hxB, hxN], by rw [hxN]⟩).1
  have hxk : ∀ t i, x t (kIdx B hB i) =
      tableauP A b B hB i + tableauQ A B hB i β * t := by
    intro t i
    simpa [mulVec, dotProduct, Pi.single_apply, mul_comm] using congrFun (hxB t) i
  have hxl : ∀ t, x t (lIdx B hB β) = t := by
    intro t; simpa using congrFun (hxN t) β
  have hxother : ∀ t j, j ≠ β → x t (lIdx B hB j) = 0 := by
    intro t j hj; simpa [Pi.single_apply, hj] using congrFun (hxN t) j
  have hcx : ∀ t, c ⬝ᵥ x t = tableauZ0 A b c B hB + tableauR A c B hB β * t := by
    intro t
    have h := ((hstd (x t) (c ⬝ᵥ x t)).mp ⟨hAx t, rfl⟩).2
    rw [hxN t] at h
    simpa [dotProduct, Pi.single_apply] using h
  have hxpos : ∀ t, 0 ≤ t →
      (∀ i, 0 ≤ tableauP A b B hB i + tableauQ A B hB i β * t) → 0 ≤ x t := by
    intro t ht hi j
    change 0 ≤ x t j
    by_cases hj : j ∈ B
    · have hj' : j ∈ Set.range (kIdx B hB) := by
        unfold kIdx; rw [Finset.range_orderEmbOfFin]; exact hj
      obtain ⟨i, rfl⟩ := hj'
      rw [hxk]; exact hi i
    · have hj' : j ∈ Set.range (lIdx B hB) := by
        unfold lIdx; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hj
      obtain ⟨i, rfl⟩ := hj'
      by_cases hi : i = β
      · subst i; rw [hxl]; exact ht
      · rw [hxother t i hi]
  constructor
  · intro α hleave
    let t : ℝ := -tableauP A b B hB α / tableauQ A B hB α β
    have ht : 0 ≤ t := div_nonneg_of_nonpos (neg_nonpos.mpr (hfeas.2 α))
      (le_of_lt hleave.2.1)
    have hp : ∀ i, 0 ≤ tableauP A b B hB i + tableauQ A B hB i β * t := by
      intro i
      by_cases hi : tableauQ A B hB i β < 0
      · have hratio := hleave.2.2 i hi
        have hbound := (le_div_iff_of_neg hi).mp hratio
        dsimp [t] at *
        nlinarith
      · have hpi := hfeas.2 i
        have hqi : 0 ≤ tableauQ A B hB i β := le_of_not_gt hi
        exact add_nonneg hpi (mul_nonneg hqi ht)
    have hxzero : x t (kIdx B hB α) = 0 := by
      rw [hxk]
      dsimp [t]
      field_simp [ne_of_lt hleave.2.1]
      ring
    have hB' : (pivotBasis B hB β α).card = m := by
      rw [pivotBasis, Finset.card_insert_of_notMem, Finset.card_erase_of_mem (TabCore.kIdx_mem B hB α)]
      · have := α.isLt
        omega
      · exact fun h => TabCore.lIdx_notMem B hB β (Finset.mem_of_mem_erase h)
    have hdet := TabCore.pivot_nonsingular A B hB hfeas.1 β α (ne_of_lt hleave.2.1) hB'
    have hxout : ∀ j, j ∉ pivotBasis B hB β α → x t j = 0 := by
      intro j hj
      by_cases hjB : j ∈ B
      · have hjα : j = kIdx B hB α := by
          by_contra hne
          exact hj (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hjB⟩))
        rw [hjα]; exact hxzero
      · have hj' : j ∈ Set.range (lIdx B hB) := by
          unfold lIdx; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hjB
        obtain ⟨i, rfl⟩ := hj'
        apply hxother
        intro hi; subst i
        exact hj (Finset.mem_insert_self _ _)
    have hxN' : (fun j => x t (lIdx (pivotBasis B hB β α) hB' j)) = 0 :=
      funext fun j => hxout _ (TabCore.lIdx_notMem _ hB' j)
    have hxB' := ((TabCore.tableau_std A b c _ hB' hdet) (x t) (c ⬝ᵥ x t)).mp ⟨hAx t, rfl⟩
    rw [hxN', mulVec_zero, add_zero] at hxB'
    refine ⟨hB', hdet, ?_⟩
    intro i
    change 0 ≤ tableauP A b (pivotBasis B hB β α) hB' i
    have h := congrFun hxB'.1 i
    rw [← h]
    exact hxpos t ht hp _
  · intro hq
    have hfeasible : ∀ t, 0 ≤ t → MatousekLP.BFS.IsFeasible A b (x t) := by
      intro t ht
      exact ⟨hAx t, hxpos t ht (fun i => add_nonneg (hfeas.2 i) (mul_nonneg (hq i) ht))⟩
    have htend : Tendsto (fun t => c ⬝ᵥ x t) atTop atTop := by
      simp_rw [hcx]
      exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hr)
    refine ⟨?_, x, ?_, hfeasible, htend⟩
    · intro M
      let t := max 0 ((M - tableauZ0 A b c B hB + 1) / tableauR A c B hB β)
      refine ⟨x t, hfeasible t (le_max_left _ _), ?_⟩
      rw [hcx]
      have hbound : (M - tableauZ0 A b c B hB + 1) / tableauR A c B hB β ≤ t := le_max_right _ _
      have hbound' := (div_le_iff₀ hr).mp hbound
      nlinarith
    · intro t; exact ⟨hAx t, hxl t, hxother t⟩
