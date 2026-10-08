-- Prove2me | solution 1 for MatousekLP.Simplex.bland_never_cycles
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:06:42.830207+00:00
-- url     : https://prove2.me/submissions/cdbead41-f100-40f6-bf4a-7009d2a3d254

import Definitions.Def_MatousekLP_Simplex_Tableau
import Mathlib

set_option autoImplicit false

open Matrix MatousekLP.Simplex

lemma BlandStep_simplex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B B' : Finset (Fin n)) (h : BlandStep A b c B B') : SimplexStep A b c B B' := by
  obtain ⟨hB, hfeas, β, α, hEL, _, _, rfl⟩ := h
  exact ⟨hB, hfeas, β, α, hEL, rfl⟩

lemma exists_lt_eq_basis_repeat {m n : ℕ} (Bs : ℕ → Finset (Fin n))
    (hsub : ∀ t, Bs t ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n))) :
    ∃ i j, i < j ∧ Bs i = Bs j := by
  classical
  set g : ℕ → {B : Finset (Fin n) // B ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n))} :=
    fun t => ⟨Bs t, hsub t⟩
  rcases Finite.exists_ne_map_eq_of_infinite g with ⟨i, j, hne, heq⟩
  rcases lt_or_gt_of_ne hne with hij | hij
  · exact ⟨i, j, hij, congrArg Subtype.val heq⟩
  · exact ⟨j, i, hij, congrArg Subtype.val heq.symm⟩

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


open Matrix MatousekLP.Simplex

theorem cycle_same_bfs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
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
lemma ivt_step (P : ℕ → Prop) (a b : ℕ) (hab : a ≤ b) (hPa : P a) (hPb : ¬ P b) :
    ∃ s, a ≤ s ∧ s < b ∧ P s ∧ ¬ P (s + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hPa hPb
  | succ b hab ih =>
    by_cases hb : P b
    · exact ⟨b, hab, Nat.lt_succ_self b, hb, hPb⟩
    · obtain ⟨s, h1, h2, h3, h4⟩ := ih hb
      exact ⟨s, h1, by omega, h3, h4⟩

lemma cyc_step (P : ℕ → Prop) (k : ℕ) (hcyc : P k ↔ P 0) (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k)
    (hPa : P a) (hPb : ¬ P b) :
    (∃ s, s < k ∧ P s ∧ ¬ P (s + 1)) ∧ (∃ s, s < k ∧ ¬ P s ∧ P (s + 1)) := by
  constructor
  · by_cases h0 : P 0
    · obtain ⟨s, _, h2, h3, h4⟩ := ivt_step P 0 b (Nat.zero_le _) h0 hPb
      exact ⟨s, by omega, h3, h4⟩
    · obtain ⟨s, _, h2, h3, h4⟩ := ivt_step P a k ha hPa (fun h => h0 (hcyc.mp h))
      exact ⟨s, h2, h3, h4⟩
  · by_cases h0 : P 0
    · obtain ⟨s, _, h2, h3, h4⟩ := ivt_step (fun s => ¬ P s) b k hb hPb
        (fun h => h (hcyc.mpr h0))
      exact ⟨s, h2, h3, not_not.mp h4⟩
    · obtain ⟨s, _, h2, h3, h4⟩ := ivt_step (fun s => ¬ P s) 0 a (Nat.zero_le _) h0
        (fun h => h hPa)
      exact ⟨s, by omega, h3, not_not.mp h4⟩

lemma pivot_leave_eq {m n : ℕ} (B : Finset (Fin n)) (hB : B.card = m) (β : Fin (n - m))
    (α : Fin m) (j : Fin n) (hj : j ∈ B) (h : j ∉ pivotBasis B hB β α) : j = kIdx B hB α := by
  by_contra hne
  apply h
  unfold pivotBasis
  exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hj⟩)

lemma pivot_enter_eq {m n : ℕ} (B : Finset (Fin n)) (hB : B.card = m) (β : Fin (n - m))
    (α : Fin m) (j : Fin n) (hj : j ∈ pivotBasis B hB β α) (h : j ∉ B) : j = lIdx B hB β := by
  unfold pivotBasis at hj
  rcases Finset.mem_insert.mp hj with h1 | h1
  · exact h1
  · exact absurd (Finset.mem_erase.mp h1).2 h

lemma leave_not_mem_pivot {m n : ℕ} (B : Finset (Fin n)) (hB : B.card = m) (β : Fin (n - m))
    (α : Fin m) : kIdx B hB α ∉ pivotBasis B hB β α := by
  simp only [pivotBasis, Finset.mem_insert, Finset.mem_erase, not_or]
  exact ⟨fun h => TabCore.lIdx_notMem B hB β (h ▸ TabCore.kIdx_mem B hB α), by simp⟩

lemma enter_mem_pivot {m n : ℕ} (B : Finset (Fin n)) (hB : B.card = m) (β : Fin (n - m))
    (α : Fin m) : lIdx B hB β ∈ pivotBasis B hB β α :=
  Finset.mem_insert_self _ _

lemma bland_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (B B' : Finset (Fin n)) (hB : B.card = m) (hB' : B'.card = m)
    (hf : IsFeasibleBasisOf A b B hB) (hf' : IsFeasibleBasisOf A b B' hB')
    (x : Fin n → ℝ) (hx : IsBasicSolutionFor A b B x) (hx' : IsBasicSolutionFor A b B' x)
    (t : Fin n) (β : Fin (n - m)) (α : Fin m)
    (hEL : IsEnteringLeaving A b c B hB β α)
    (hleave : ∀ i, IsEnteringLeaving A b c B hB β i → kIdx B hB α ≤ kIdx B hB i)
    (htα : kIdx B hB α = t) (hvt : lIdx B hB β ≤ t)
    (β' : Fin (n - m)) (htβ' : lIdx B' hB' β' = t)
    (hr' : 0 < tableauR A c B' hB' β')
    (hent' : ∀ j, 0 < tableauR A c B' hB' j → lIdx B' hB' β' ≤ lIdx B' hB' j)
    (hmax : ∀ j, j ∈ B → j ∉ B' → j ≤ t) : False := by
  classical
  have hdet := hf.1
  have hdet' := hf'.1
  have hpx := basic_tableau A b c B hB hdet x hx
  have hpx' := basic_tableau A b c B' hB' hdet' x hx'
  have hp0 : ∀ i, kIdx B hB i ∉ B' → tableauP A b B hB i = 0 := by
    intro i hi
    rw [← congrFun hpx.1 i]
    exact hx'.2 _ hi
  have hpnn : ∀ i, 0 ≤ tableauP A b B hB i := fun i => hf.2 i
  have hQ : ∀ i, kIdx B hB i ∉ B' → i ≠ α → 0 ≤ tableauQ A B hB i β := by
    intro i hi hne
    by_contra hneg
    push_neg at hneg
    have hEL_i : IsEnteringLeaving A b c B hB β i := by
      refine ⟨hEL.1, hneg, ?_⟩
      intro i' hi'
      rw [hp0 i hi, neg_zero, zero_div]
      exact div_nonneg_of_nonpos (neg_nonpos.mpr (hpnn i')) hi'.le
    have h1 := hleave i hEL_i
    have h2 := hmax _ (TabCore.kIdx_mem B hB i) hi
    rw [htα] at h1
    have h3 : kIdx B hB i = kIdx B hB α := by rw [htα]; exact le_antisymm h2 h1
    exact hne ((B.orderEmbOfFin hB).injective h3)
  set e : Fin (n - m) → ℝ := Pi.single β 1 with he
  obtain ⟨y, hyB, hyN⟩ := TabCore.exists_of_parts B hB
    (tableauP A b B hB + tableauQ A B hB *ᵥ e) e
  have hy := (TabCore.tableau_std A b c B hB hdet y
    (tableauZ0 A b c B hB + tableauR A c B hB ⬝ᵥ e)).mpr ⟨by rw [hyB, hyN], by rw [hyN]⟩
  have hz := ((TabCore.tableau_std A b c B' hB' hdet' y (c ⬝ᵥ y)).mp ⟨hy.1, rfl⟩).2
  have hz0 : tableauZ0 A b c B hB = tableauZ0 A b c B' hB' := by
    rw [← hpx.2, ← hpx'.2]
  have hre : tableauR A c B hB ⬝ᵥ e = tableauR A c B hB β := by simp [e]
  have hyBi : ∀ i, y (kIdx B hB i) = tableauP A b B hB i + tableauQ A B hB i β := by
    intro i
    have := congrFun hyB i
    simpa [mulVec, dotProduct, e, Pi.single_apply] using this
  have hyNj : ∀ j, y (lIdx B hB j) = e j := fun j => congrFun hyN j
  have hval : ∀ w, w ∉ B' → (w = t → y w < 0) ∧ (w < t → 0 ≤ y w) ∧ (t < w → y w = 0) := by
    intro w hw
    by_cases hwB : w ∈ B
    · have hw' : w ∈ Set.range (kIdx B hB) := by
        unfold kIdx; rw [Finset.range_orderEmbOfFin]; exact hwB
      obtain ⟨i, rfl⟩ := hw'
      have hyi := hyBi i
      rw [hp0 i hw, zero_add] at hyi
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have hiα : i = α := (B.orderEmbOfFin hB).injective (h.trans htα.symm)
        subst hiα
        rw [hyi]; exact hEL.2.1
      · intro h
        have hne : i ≠ α := by
          intro hiα; subst hiα; rw [htα] at h; exact lt_irrefl _ h
        rw [hyi]; exact hQ i hw hne
      · intro h
        exact absurd (hmax _ hwB hw) (not_le.mpr h)
    · have hw' : w ∈ Set.range (lIdx B hB) := by
        unfold lIdx; rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.mpr hwB
      obtain ⟨j, rfl⟩ := hw'
      have hyj := hyNj j
      refine ⟨?_, ?_, ?_⟩
      · intro h
        exact absurd (h ▸ htα ▸ TabCore.kIdx_mem B hB α) hwB
      · intro _
        rw [hyj]
        simp only [e, Pi.single_apply]
        split_ifs <;> norm_num
      · intro h
        have hjβ : j ≠ β := by
          intro hjβ; subst hjβ; exact absurd (lt_of_le_of_lt hvt h) (lt_irrefl _)
        rw [hyj]
        simp [e, Pi.single_apply, hjβ]
  have hterm : ∀ j, tableauR A c B' hB' j * y (lIdx B' hB' j) ≤ 0 := by
    intro j
    have hw := hval _ (TabCore.lIdx_notMem B' hB' j)
    rcases lt_trichotomy (lIdx B' hB' j) t with hlt | heq | hgt
    · have hr : tableauR A c B' hB' j ≤ 0 := by
        by_contra hpos
        push_neg at hpos
        have := hent' j hpos
        rw [htβ'] at this
        exact absurd hlt (not_lt.mpr this)
      have hy0 := hw.2.1 hlt
      have := mul_nonneg (neg_nonneg.mpr hr) hy0
      linarith
    · have hy0 := hw.1 heq
      have hjβ : j = β' := (B'ᶜ.orderEmbOfFin (card_compl_eq hB')).injective (heq.trans htβ'.symm)
      subst hjβ
      have := mul_pos hr' (neg_pos.mpr hy0)
      linarith
    · rw [hw.2.2 hgt, mul_zero]
  have hterm_neg : tableauR A c B' hB' β' * y (lIdx B' hB' β') < 0 := by
    have hy0 := (hval _ (TabCore.lIdx_notMem B' hB' β')).1 htβ'
    have := mul_pos hr' (neg_pos.mpr hy0)
    linarith
  have hsum : tableauR A c B' hB' ⬝ᵥ (fun j => y (lIdx B' hB' j)) < 0 := by
    have : tableauR A c B' hB' ⬝ᵥ (fun j => y (lIdx B' hB' j)) =
        ∑ j, tableauR A c B' hB' j * y (lIdx B' hB' j) := rfl
    rw [this]
    calc ∑ j, tableauR A c B' hB' j * y (lIdx B' hB' j)
        < ∑ _j : Fin (n - m), (0 : ℝ) :=
          Finset.sum_lt_sum (fun j _ => hterm j) ⟨β', Finset.mem_univ _, hterm_neg⟩
      _ = 0 := by simp
  have h1 := hy.2
  rw [hre, hz, ← hz0] at h1
  have := hEL.1
  linarith

lemma bland_cycle_false {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) (k : ℕ) (hk : 1 ≤ k)
    (Bs : ℕ → Finset (Fin n)) (hBl : ∀ s, s < k → BlandStep A b c (Bs s) (Bs (s + 1)))
    (hcycle : Bs k = Bs 0) : False := by
  classical
  obtain ⟨x, _, hbas, _⟩ := cycle_same_bfs A b c hmn hrank k hk Bs
    (fun s hs => BlandStep_simplex A b c _ _ (hBl s hs)) hcycle
  let S : Finset (Fin n) := Finset.univ.filter
    (fun j => ∃ a, a ≤ k ∧ ∃ b', b' ≤ k ∧ j ∈ Bs a ∧ j ∉ Bs b')
  have hne : S.Nonempty := by
    obtain ⟨hB, _, β, α, _, _, _, hpiv⟩ := hBl 0 (by omega)
    refine ⟨kIdx (Bs 0) hB α, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨0, Nat.zero_le _, 1, hk, TabCore.kIdx_mem _ hB α, ?_⟩
    rw [hpiv]
    exact leave_not_mem_pivot _ hB β α
  set t := S.max' hne with ht
  have htS : t ∈ S := Finset.max'_mem _ _
  have hmax : ∀ a, a ≤ k → ∀ b', b' ≤ k → ∀ j, j ∈ Bs a → j ∉ Bs b' → j ≤ t := by
    intro a ha b' hb' j hja hjb
    refine Finset.le_max' S j ?_
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha, b', hb', hja, hjb⟩
  obtain ⟨a, ha, b', hb', hta, htb⟩ : ∃ a, a ≤ k ∧ ∃ b', b' ≤ k ∧ t ∈ Bs a ∧ t ∉ Bs b' := by
    simpa [S] using htS
  obtain ⟨⟨s, hs, hs1, hs2⟩, ⟨s', hs', hs'1, hs'2⟩⟩ :=
    cyc_step (fun s => t ∈ Bs s) k (by show t ∈ Bs k ↔ t ∈ Bs 0; rw [hcycle]) a b' ha hb'
      hta htb
  have hs1 : t ∈ Bs s := hs1
  have hs2 : t ∉ Bs (s + 1) := hs2
  have hs'1 : t ∉ Bs s' := hs'1
  have hs'2 : t ∈ Bs (s' + 1) := hs'2
  obtain ⟨hB, hf, β, α, hEL, _, hleave, hpiv⟩ := hBl s hs
  have htα : kIdx (Bs s) hB α = t :=
    (pivot_leave_eq (Bs s) hB β α t hs1 (by rw [← hpiv]; exact hs2)).symm
  have hvt : lIdx (Bs s) hB β ≤ t :=
    hmax (s + 1) (by omega) s (by omega) _ (by rw [hpiv]; exact enter_mem_pivot _ hB β α)
      (TabCore.lIdx_notMem _ hB β)
  obtain ⟨hB', hf', β2, α2, hEL2, hent2, _, hpiv2⟩ := hBl s' hs'
  have htβ : lIdx (Bs s') hB' β2 = t :=
    (pivot_enter_eq (Bs s') hB' β2 α2 t (by rw [← hpiv2]; exact hs'2) hs'1).symm
  exact bland_core A b c (Bs s) (Bs s') hB hB' hf hf' x (hbas s hs.le) (hbas s' hs'.le) t β α
    hEL hleave htα hvt β2 htβ hEL2.1 hent2 (fun j hj hj' => hmax s hs.le s' hs'.le j hj hj')

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hmn : m ≤ n) (hrank : A.rank = m) :
    ¬ ∃ Bs : ℕ → Finset (Fin n), ∀ t, BlandStep A b c (Bs t) (Bs (t + 1)) := by
  classical
  rintro ⟨Bs, hBland⟩
  have hsub : ∀ t, Bs t ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)) := by
    intro t
    obtain ⟨hB, _⟩ := hBland t
    exact Finset.mem_powersetCard.mpr ⟨fun j _ => Finset.mem_univ j, hB⟩
  obtain ⟨i, j, hij, heq⟩ := exists_lt_eq_basis_repeat Bs hsub
  have hk : 1 ≤ j - i := by omega
  have hcycle : Bs (i + (j - i)) = Bs i := by
    rw [Nat.add_sub_cancel' (by omega : i ≤ j)]
    exact heq.symm
  exact bland_cycle_false A b c hmn hrank (j - i) hk (fun t => Bs (i + t))
    (fun t _ => hBland (i + t)) hcycle
