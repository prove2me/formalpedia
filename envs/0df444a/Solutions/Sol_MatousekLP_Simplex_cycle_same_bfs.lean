-- Prove2me | solution 1 for MatousekLP.Simplex.cycle_same_bfs
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T23:50:12.173508+00:00
-- url     : https://prove2.me/submissions/e80ace53-d1a5-40e7-b159-66899f752148

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

open Matrix MatousekLP.Simplex


lemma basic_tableau {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (B : Finset (Fin n)) (hB : B.card = m)
    (hdet : IsUnit (basisMatrix A B hB).det) (x : Fin n → ℝ)
    (hx : IsBasicSolutionFor A b B x) :
    (fun i => x (kIdx B hB i)) = tableauP A b B hB ∧
      c ⬝ᵥ x = tableauZ0 A b c B hB := by
  have hxN : (fun j => x (lIdx B hB j)) = 0 :=
    funext fun j => hx.2 _ (TabCore.lIdx_notMem B hB j)
  have h := (TabCore.tableau_std A b c B hB hdet x (c ⬝ᵥ x)).mp ⟨hx.1, rfl⟩
  simpa [hxN] using h

lemma basic_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (B : Finset (Fin n)) (hB : B.card = m)
    (hdet : IsUnit (basisMatrix A B hB).det) (x y : Fin n → ℝ)
    (hx : IsBasicSolutionFor A b B x) (hy : IsBasicSolutionFor A b B y) : x = y := by
  have hxB := (basic_tableau A b 0 B hB hdet x hx).1
  have hyB := (basic_tableau A b 0 B hB hdet y hy).1
  funext j
  by_cases hj : j ∈ B
  · have hj' : j ∈ Set.range (kIdx B hB) := by
      unfold kIdx
      rw [Finset.range_orderEmbOfFin]
      exact hj
    obtain ⟨i, rfl⟩ := hj'
    exact (congrFun hxB i).trans (congrFun hyB i).symm
  · rw [hx.2 j hj, hy.2 j hj]

lemma feasible_basic_exists {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (B : Finset (Fin n)) (hB : IsFeasibleBasis A b B) :
    ∃ x, MatousekLP.BFS.IsFeasible A b x ∧ IsBasicSolutionFor A b B x := by
  obtain ⟨hcard, ⟨hdet, hpos⟩⟩ := hB
  obtain ⟨x, hxB, hxN⟩ := TabCore.exists_of_parts B hcard (tableauP A b B hcard) 0
  have hAx : A *ᵥ x = b :=
    ((TabCore.tableau_std A b 0 B hcard hdet) x 0).mpr
      ⟨by simp [hxB, hxN], by simp [hxN, tableauZ0]⟩ |>.1
  have hout : ∀ j, j ∉ B → x j = 0 := by
    intro j hj
    have hj' : j ∈ Set.range (lIdx B hcard) := by
      unfold lIdx
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.mpr hj
    obtain ⟨i, rfl⟩ := hj'
    exact congrFun hxN i
  refine ⟨x, ⟨hAx, ?_⟩, hAx, hout⟩
  intro j
  change 0 ≤ x j
  by_cases hj : j ∈ B
  · have hj' : j ∈ Set.range (kIdx B hcard) := by
      unfold kIdx
      rw [Finset.range_orderEmbOfFin]
      exact hj
    obtain ⟨i, rfl⟩ := hj'
    rw [congrFun hxB i]
    exact hpos i
  · rw [hout j hj]

/-- The objective cannot decrease in a pivot, and equality forces the two BFSs to agree. -/
lemma step_objective {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (B B' : Finset (Fin n))
    (hstep : SimplexStep A b c B B') (x y : Fin n → ℝ)
    (hx : IsBasicSolutionFor A b B x) (hy : IsBasicSolutionFor A b B' y)
    (hypos : 0 ≤ y) :
    c ⬝ᵥ x ≤ c ⬝ᵥ y ∧ (c ⬝ᵥ x = c ⬝ᵥ y → x = y) := by
  classical
  obtain ⟨hB, hfeas, β, α, hleave, rfl⟩ := hstep
  have hN : ∀ j, j ≠ β → lIdx B hB j ∉ pivotBasis B hB β α := by
    intro j hj
    simp only [pivotBasis, Finset.mem_insert, Finset.mem_erase, not_or]
    refine ⟨?_, fun h => TabCore.lIdx_notMem B hB j h.2⟩
    exact fun h => hj ((Bᶜ.orderEmbOfFin (card_compl_eq hB)).injective h)
  have hyN : (fun j => y (lIdx B hB j)) = Pi.single β (y (lIdx B hB β)) := by
    funext j
    by_cases hj : j = β
    · subst j; simp
    · simp [hj, hy.2 _ (hN j hj)]
  have hcx := (basic_tableau A b c B hB hfeas.1 x hx).2
  have hcy : c ⬝ᵥ y = tableauZ0 A b c B hB +
      tableauR A c B hB β * y (lIdx B hB β) := by
    have h := ((TabCore.tableau_std A b c B hB hfeas.1) y (c ⬝ᵥ y)).mp ⟨hy.1, rfl⟩
    rw [hyN] at h
    simpa [dotProduct, Pi.single_apply] using h.2
  have hnonneg := hypos (lIdx B hB β)
  have hr := hleave.1
  refine ⟨?_, ?_⟩
  · rw [hcx, hcy]
    exact le_add_of_nonneg_right (mul_nonneg (le_of_lt hr) hnonneg)
  · intro heq
    have hzero : y (lIdx B hB β) = 0 := by
      rw [hcx, hcy] at heq
      nlinarith
    apply basic_unique A b B hB hfeas.1 x y hx
    refine ⟨hy.1, ?_⟩
    intro j hj
    have hj' : j ∈ Set.range (lIdx B hB) := by
      unfold lIdx
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.mpr hj
    obtain ⟨i, rfl⟩ := hj'
    simpa [hzero] using congrFun hyN i

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (k : ℕ) (hk : 1 ≤ k)
    (Bs : ℕ → Finset (Fin n)) (hstep : ∀ t, t < k → SimplexStep A b c (Bs t) (Bs (t + 1)))
    (hcycle : Bs k = Bs 0) :
    ∃ x : Fin n → ℝ, MatousekLP.BFS.IsFeasible A b x ∧
      (∀ t, t ≤ k → IsBasicSolutionFor A b (Bs t) x) ∧
      ∀ t, t < k → ∀ j, j ∈ Bs (t + 1) → j ∉ Bs t → x j = 0 := by
  classical
  have hfeas : ∀ t, t ≤ k → IsFeasibleBasis A b (Bs t) := by
    intro t ht
    by_cases hlt : t < k
    · obtain ⟨hB, hBfeas, _⟩ := hstep t hlt
      exact ⟨hB, hBfeas⟩
    · have htk : t = k := by omega
      rw [htk, hcycle]
      obtain ⟨hB, hBfeas, _⟩ := hstep 0 (by omega)
      exact ⟨hB, hBfeas⟩
  have hex : ∀ t, ∃ x, MatousekLP.BFS.IsFeasible A b x ∧
      IsBasicSolutionFor A b (Bs (min t k)) x := by
    intro t
    exact feasible_basic_exists A b _ (hfeas _ (min_le_right _ _))
  choose xs hxs using hex
  have hx : ∀ t, t ≤ k → MatousekLP.BFS.IsFeasible A b (xs t) ∧
      IsBasicSolutionFor A b (Bs t) (xs t) := by
    intro t ht
    simpa [min_eq_left ht] using hxs t
  have hobjstep : ∀ t, t < k → c ⬝ᵥ xs t ≤ c ⬝ᵥ xs (t + 1) ∧
      (c ⬝ᵥ xs t = c ⬝ᵥ xs (t + 1) → xs t = xs (t + 1)) := by
    intro t ht
    exact step_objective A b c _ _ (hstep t ht) _ _
      (hx t (by omega)).2 (hx (t + 1) (by omega)).2 (hx (t + 1) (by omega)).1.2
  have hmono : Monotone (fun t => c ⬝ᵥ xs (min t k)) := by
    apply monotone_nat_of_le_succ
    intro t
    by_cases ht : t < k
    · simpa [min_eq_left (show t ≤ k by omega),
        min_eq_left (show t + 1 ≤ k by omega)] using (hobjstep t ht).1
    · simp [min_eq_right (show k ≤ t by omega),
        min_eq_right (show k ≤ t + 1 by omega)]
  have hclose : xs k = xs 0 := by
    obtain ⟨hB, hBfeas⟩ := hfeas 0 (by omega)
    apply basic_unique A b (Bs 0) hB hBfeas.1
    · simpa [hcycle] using (hx k le_rfl).2
    · exact (hx 0 (by omega)).2
  have hobj : ∀ t, t ≤ k → c ⬝ᵥ xs t = c ⬝ᵥ xs 0 := by
    intro t ht
    have hlo := hmono (show 0 ≤ t by omega)
    have hhi := hmono ht
    simp only [Nat.zero_min, min_eq_left ht, min_self, hclose] at hlo hhi
    exact le_antisymm hhi hlo
  have heq : ∀ t, t ≤ k → xs t = xs 0 := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have hsame := (hobjstep t (by omega)).2
        ((hobj t (by omega)).trans (hobj (t + 1) ht).symm)
      exact hsame.symm.trans (ih (by omega))
  refine ⟨xs 0, (hx 0 (by omega)).1, ?_, ?_⟩
  · intro t ht
    simpa [heq t ht] using (hx t ht).2
  · intro t ht j _ hj
    exact ((show IsBasicSolutionFor A b (Bs t) (xs 0) by
      simpa [heq t (by omega)] using (hx t (by omega)).2)).2 j hj
