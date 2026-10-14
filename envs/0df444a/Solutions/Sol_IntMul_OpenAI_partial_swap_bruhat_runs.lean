-- Prove2me | solution 1 for IntMul.OpenAI.partial_swap_bruhat_runs
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:38:36.976596+00:00
-- url     : https://prove2.me/submissions/e940b731-a26e-4e43-a13a-dd5a00f24c8d

import Mathlib

section Sec_PSwap


namespace PSwapAux
open Submodule Module

variable {K : Type*} [Field K]

lemma finrank_span_union_units {R ι : Type*} [Fintype R] [DecidableEq R] (P : R → Prop)
    [DecidablePred P] (v : ι → R → K) :
    finrank K (span K (Set.range v ∪ {w | ∃ r, P r ∧ w = Pi.single r 1})) =
      Fintype.card {r // P r} +
        finrank K (span K (Set.range fun i (r : {r // ¬ P r}) => v i r.1)) := by
  set W := span K (Set.range v ∪ {w | ∃ r, P r ∧ w = Pi.single r 1}) with hW
  let π : (R → K) →ₗ[K] ({r // ¬ P r} → K) := LinearMap.funLeft K K Subtype.val
  have h1 := LinearMap.finrank_range_add_finrank_ker (π.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have hmap : W.map π = span K (Set.range fun i (r : {r // ¬ P r}) => v i r.1) := by
    rw [hW, Submodule.map_span]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨w, hw | ⟨r, hr, rfl⟩, rfl⟩
      · obtain ⟨i, rfl⟩ := hw
        exact subset_span ⟨i, rfl⟩
      · have : π (Pi.single r 1) = 0 := by
          funext x
          have hx : x.1 ≠ r := fun h => x.2 (h ▸ hr)
          simp [π, LinearMap.funLeft_apply, hx]
        rw [SetLike.mem_coe, this]
        exact zero_mem _
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      exact subset_span ⟨v i, Or.inl ⟨i, rfl⟩, rfl⟩
  have hker : LinearMap.ker π ≤ W := by
    intro x hx
    have hx' : ∀ r : {r // ¬ P r}, x r.1 = 0 := fun r => congrFun hx r
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : P i
    · have : Pi.single i (x i) = x i • (Pi.single i (1 : K) : R → K) := by
        ext j; simp [Pi.single_apply]
      rw [this]
      exact smul_mem _ _ (subset_span (Or.inr ⟨i, hi, rfl⟩))
    · rw [hx' ⟨i, hi⟩, Pi.single_zero]
      exact zero_mem _
  have h2 : finrank K ((LinearMap.ker π).comap W.subtype) = finrank K (LinearMap.ker π) :=
    (comapSubtypeEquivOfLe hker).finrank_eq
  have h3 := LinearMap.finrank_range_add_finrank_ker π
  have hsurj : LinearMap.range π = ⊤ :=
    LinearMap.range_eq_top.2 (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective)
  rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype_compl] at h3
  have h4 := Fintype.card_subtype_le P
  rw [hmap, h2] at h1
  omega


lemma rank_eq_of_range_rows {m m' n : Type*} [Fintype m] [Fintype m'] [Fintype n]
    {A : Matrix m n K} {B : Matrix m' n K} (h : Set.range A.row = Set.range B.row) : A.rank = B.rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, h]

lemma rank_eq_of_range_cols {m n n' : Type*} [Fintype m] [Fintype n] [Fintype n']
    {A : Matrix m n K} {B : Matrix m n' K} (h : Set.range A.col = Set.range B.col) :
    A.rank = B.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, h]

lemma partB {m : ℕ} (p : Matrix (Fin m) (Fin m) K) (X Y : ℕ) :
    (Matrix.of fun (r : {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun c => (1 - p) r.1 c.1) (fun c => p r.1 c) c).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val ∧ c.val < X).card +
      (p.submatrix (fun r : {r : Fin m // r.val < min X Y} => r.1) id).rank := by
  set M := (Matrix.of fun (r : {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun c => (1 - p) r.1 c.1) (fun c => p r.1 c) c) with hM
  let P : {r : Fin m // r.val < X} → Prop := fun r => Y ≤ r.1.val
  let v : Fin m → {r : Fin m // r.val < X} → K := fun j r => p r.1 j
  have hspan : span K (Set.range M.col) = span K (Set.range v ∪ {w | ∃ r, P r ∧ w = Pi.single r 1}) := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨c, rfl⟩
      rcases c with c | c
      · by_cases hc : c.1.val < X
        · have : M.col (Sum.inl c) = (Pi.single ⟨c.1, hc⟩ 1 : _ → K) - v c.1 := by
            funext r
            simp [hM, v, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, Subtype.ext_iff,
              eq_comm]
          rw [SetLike.mem_coe, this]
          exact sub_mem (subset_span (Or.inr ⟨_, c.2, rfl⟩)) (subset_span (Or.inl ⟨c.1, rfl⟩))
        · have : M.col (Sum.inl c) = - v c.1 := by
            funext r
            have : r.1 ≠ c.1 := fun h => hc (h ▸ r.2)
            simp [hM, v, Matrix.sub_apply, Matrix.one_apply, this]
          rw [SetLike.mem_coe, this]
          exact neg_mem (subset_span (Or.inl ⟨c.1, rfl⟩))
      · exact subset_span (Or.inl ⟨c, rfl⟩)
    · rw [span_le]
      rintro _ (⟨j, rfl⟩ | ⟨r, hr, rfl⟩)
      · exact subset_span ⟨Sum.inr j, rfl⟩
      · have : (Pi.single r 1 : _ → K) = M.col (Sum.inl ⟨r.1, hr⟩) + M.col (Sum.inr r.1) := by
          funext r'
          simp [hM, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, Subtype.ext_iff]
        rw [SetLike.mem_coe, this]
        exact add_mem (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩)
  rw [Matrix.rank_eq_finrank_span_cols, hspan, finrank_span_union_units]
  congr 1
  · rw [← Fintype.card_subtype]
    exact Fintype.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun r : Fin m => r.val < X)
      (fun r => Y ≤ r.val)).trans (Equiv.subtypeEquivRight fun _ => and_comm))
  · refine Eq.trans (Matrix.rank_eq_finrank_span_cols
      (Matrix.of fun (r : {r // ¬ P r}) (j : Fin m) => p r.1.1 j)).symm ?_
    apply rank_eq_of_range_rows
    ext w
    constructor
    · rintro ⟨⟨r, hr⟩, rfl⟩
      exact ⟨⟨r.1, lt_min r.2 (not_le.1 hr)⟩, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨⟨⟨r.1, lt_of_lt_of_le r.2 (min_le_left _ _)⟩,
        not_le.2 (lt_of_lt_of_le r.2 (min_le_right _ _))⟩, rfl⟩

lemma partC {m : ℕ} (p : Matrix (Fin m) (Fin m) K) (X Y : ℕ) :
    (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val}) =>
        Sum.elim (fun r => p r c.1) (fun r => (1 - p) r.1 c.1) r).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val ∧ c.val < X).card +
      (p.submatrix id (fun c : {c : Fin m // max X Y ≤ c.val} => c.1)).rank := by
  set M := (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val}) =>
        Sum.elim (fun r => p r c.1) (fun r => (1 - p) r.1 c.1) r) with hM
  let P : {c : Fin m // Y ≤ c.val} → Prop := fun c => c.1.val < X
  let v : Fin m → {c : Fin m // Y ≤ c.val} → K := fun r c => p r c.1
  have hspan : span K (Set.range M.row) =
      span K (Set.range v ∪ {w | ∃ r, P r ∧ w = Pi.single r 1}) := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨r, rfl⟩
      rcases r with r | r
      · exact subset_span (Or.inl ⟨r, rfl⟩)
      · by_cases hr : Y ≤ r.1.val
        · have : M.row (Sum.inr r) = (Pi.single ⟨r.1, hr⟩ 1 : _ → K) - v r.1 := by
            funext c
            simp [hM, v, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, Subtype.ext_iff, eq_comm]
          rw [SetLike.mem_coe, this]
          exact sub_mem (subset_span (Or.inr ⟨_, r.2, rfl⟩)) (subset_span (Or.inl ⟨r.1, rfl⟩))
        · have : M.row (Sum.inr r) = - v r.1 := by
            funext c
            have : r.1 ≠ c.1 := fun h => hr (h ▸ c.2)
            simp [hM, v, Matrix.sub_apply, Matrix.one_apply, this]
          rw [SetLike.mem_coe, this]
          exact neg_mem (subset_span (Or.inl ⟨r.1, rfl⟩))
    · rw [span_le]
      rintro _ (⟨j, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact subset_span ⟨Sum.inl j, rfl⟩
      · have : (Pi.single c 1 : _ → K) = M.row (Sum.inr ⟨c.1, hc⟩) + M.row (Sum.inl c.1) := by
          funext c'
          simp [hM, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply, Subtype.ext_iff, eq_comm]
        rw [SetLike.mem_coe, this]
        exact add_mem (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩)
  rw [Matrix.rank_eq_finrank_span_row, hspan, finrank_span_union_units]
  congr 1
  · rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun r : Fin m => Y ≤ r.val)
      (fun r => r.val < X))
  · refine Eq.trans (Matrix.rank_eq_finrank_span_row
      (Matrix.of fun (r : Fin m) (c : {c // ¬ P c}) => p r c.1.1)).symm ?_
    apply rank_eq_of_range_cols
    ext w
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact ⟨⟨c.1, max_le (not_lt.1 hc) c.2⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨⟨⟨c.1, le_trans (le_max_right _ _) c.2⟩,
        not_lt.2 (le_trans (le_max_left _ _) c.2)⟩, rfl⟩

lemma sq_one_sub_two {m : ℕ} (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p) :
    (1 - p - p) * (1 - p - p) = 1 := by
  have : (1 - p - p) * (1 - p - p) = 1 - 4 • p + 4 • (p * p) := by noncomm_ring
  rw [this, hp]; abel

lemma mul_one_sub_two {m : ℕ} (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p) :
    p * (1 - p - p) = -p := by
  have : p * (1 - p - p) = p - 2 • (p * p) := by noncomm_ring
  rw [this, hp]; abel

def PD (m X Y : ℕ) : Fin m ⊕ {r : Fin m // r.val < X} → Prop :=
  Sum.elim (fun r => Y ≤ r.val) (fun _ => False)

instance (m X Y : ℕ) : DecidablePred (PD m X Y) := fun i => by
  cases i <;> (simp only [PD, Sum.elim_inl, Sum.elim_inr]; infer_instance)

def QD (m X : ℕ) : Fin m → Prop := fun j => j.val < X

instance (m X : ℕ) : DecidablePred (QD m X) := fun j => by
  simp only [QD]; infer_instance

lemma partD {m : ℕ} (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p) (X Y : ℕ) :
    (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun r => Sum.elim (fun c => (1 - p) r c.1) (fun c => p r c) c)
          (fun r => Sum.elim (fun c => p r.1 c.1) (fun c => (1 - p) r.1 c) c) r).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val).card + min X m +
      (p.submatrix (fun r : {r : Fin m // r.val < Y} => r.1)
        (fun c : {c : Fin m // X ≤ c.val} => c.1)).rank := by
  set M := (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X})
      (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun r => Sum.elim (fun c => (1 - p) r c.1) (fun c => p r c) c)
          (fun r => Sum.elim (fun c => p r.1 c.1) (fun c => (1 - p) r.1 c) c) r) with hM
  -- row operation: subtract H-row r from D-row r
  set M1 : Matrix (Fin m ⊕ {r : Fin m // r.val < X}) ({c : Fin m // Y ≤ c.val} ⊕ Fin m) K :=
    Matrix.of fun i c => M i c - Sum.elim (fun _ => 0) (fun r => M (Sum.inl r.1) c) i with hM1
  have h1 : M.rank = M1.rank := by
    rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
    suffices hs : span K (Set.range M.row) = span K (Set.range M1.row) by rw [hs]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with r | r
      · have : M.row (Sum.inl r) = M1.row (Sum.inl r) := by
          funext c; simp [hM1]
        rw [SetLike.mem_coe, this]; exact subset_span ⟨_, rfl⟩
      · have : M.row (Sum.inr r) = M1.row (Sum.inr r) + M1.row (Sum.inl r.1) := by
          funext c; simp [hM1]
        rw [SetLike.mem_coe, this]
        exact add_mem (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩)
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with r | r
      · have : M1.row (Sum.inl r) = M.row (Sum.inl r) := by
          funext c; simp [hM1]
        rw [SetLike.mem_coe, this]; exact subset_span ⟨_, rfl⟩
      · have : M1.row (Sum.inr r) = M.row (Sum.inr r) - M.row (Sum.inl r.1) := by
          funext c; simp [hM1]
        rw [SetLike.mem_coe, this]
        exact sub_mem (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩)
  -- column operation: unit columns
  let P := PD m X Y
  let v : Fin m → Fin m ⊕ {r : Fin m // r.val < X} → K := fun j => M1.col (Sum.inr j)
  have hspan1 : span K (Set.range M1.col) =
      span K (Set.range v ∪ {w | ∃ r, P r ∧ w = Pi.single r 1}) := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨c, rfl⟩
      rcases c with c | c
      · have : M1.col (Sum.inl c) = (Pi.single (Sum.inl c.1) 1 : _ → K) - v c.1 := by
          funext i
          rcases i with r | r
          · simp [hM1, hM, v, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
          · simp [hM1, hM, v, Matrix.sub_apply, Matrix.one_apply]
        rw [SetLike.mem_coe, this]
        exact sub_mem (subset_span (Or.inr ⟨Sum.inl c.1, c.2, rfl⟩)) (subset_span (Or.inl ⟨c.1, rfl⟩))
      · exact subset_span (Or.inl ⟨c, rfl⟩)
    · rw [span_le]
      rintro _ (⟨j, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact subset_span ⟨Sum.inr j, rfl⟩
      · rcases i with c | r
        · have : (Pi.single (Sum.inl c) 1 : _ → K) =
              M1.col (Sum.inl ⟨c, hi⟩) + M1.col (Sum.inr c) := by
            funext i
            rcases i with r | r
            · simp [hM1, hM, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
            · simp [hM1, hM, Matrix.sub_apply, Matrix.one_apply]
          rw [SetLike.mem_coe, this]
          exact add_mem (subset_span ⟨_, rfl⟩) (subset_span ⟨_, rfl⟩)
        · exact hi.elim
  have hcard1 : Fintype.card {i // P i} = (Finset.univ.filter fun c : Fin m => Y ≤ c.val).card := by
    have hz : ∑ a : {r : Fin m // r.val < X}, (if P (Sum.inr a) then (1 : ℕ) else 0) = 0 :=
      Finset.sum_eq_zero fun r _ => if_neg id
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type, Finset.card_filter, hz,
      add_zero]
    exact Finset.sum_congr rfl fun r _ => by simp [P, PD]
  -- the remaining matrix
  set S : Matrix (Fin m) (Fin m) K := 1 - p - p with hS
  set N2 : Matrix ({r : Fin m // r.val < Y} ⊕ {r : Fin m // r.val < X}) (Fin m) K :=
    Matrix.of fun i j => Sum.elim (fun r => p r.1 j) (fun r => S r.1 j) i with hN2
  have h2 : finrank K (span K (Set.range fun j (i : {i // ¬ P i}) => v j i.1)) = N2.rank := by
    refine Eq.trans (Matrix.rank_eq_finrank_span_cols
      (Matrix.of fun (i : {i // ¬ P i}) (j : Fin m) => v j i.1)).symm ?_
    apply rank_eq_of_range_rows
    ext w
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      rcases i with r | r
      · refine ⟨Sum.inl ⟨r, not_le.1 hi⟩, ?_⟩
        funext j; simp [hN2, v, hM1, hM]
      · refine ⟨Sum.inr r, ?_⟩
        funext j; simp [hN2, v, hM1, hM, hS, Matrix.sub_apply, Matrix.one_apply]
    · rintro ⟨i, rfl⟩
      rcases i with r | r
      · refine ⟨⟨Sum.inl r.1, not_le.2 r.2⟩, ?_⟩
        funext j; simp [hN2, v, hM1, hM]
      · refine ⟨⟨Sum.inr r, not_false⟩, ?_⟩
        funext j; simp [hN2, v, hM1, hM, hS, Matrix.sub_apply, Matrix.one_apply]
  have hSS : S * S = 1 := sq_one_sub_two p hp
  have h3 : N2.rank = (N2 * S).rank := by
    apply le_antisymm
    · have : N2 = N2 * S * S := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      calc N2.rank = (N2 * S * S).rank := by rw [← this]
        _ ≤ (N2 * S).rank := Matrix.rank_mul_le_left _ _
    · exact Matrix.rank_mul_le_left _ _
  let Q := QD m X
  let w : {r : Fin m // r.val < Y} → Fin m → K := fun r j => p r.1 j
  have hrowL : ∀ r, (N2 * S).row (Sum.inl r) = - w r := by
    intro r; funext j
    have := congrFun (congrFun (mul_one_sub_two p hp) r.1) j
    simp only [Matrix.mul_apply, Matrix.neg_apply] at this
    simp [Matrix.mul_apply, hN2, w, ← this, hS]
  have hrowR : ∀ r, (N2 * S).row (Sum.inr r) = Pi.single r.1 1 := by
    intro r; funext j
    have := congrFun (congrFun hSS r.1) j
    simp only [Matrix.mul_apply] at this
    simp [Matrix.mul_apply, hN2, this, Matrix.one_apply, Pi.single_apply, eq_comm]
  have hspan2 : span K (Set.range (N2 * S).row) =
      span K (Set.range w ∪ {u | ∃ j, Q j ∧ u = Pi.single j 1}) := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with r | r
      · rw [SetLike.mem_coe, hrowL]
        exact neg_mem (subset_span (Or.inl ⟨r, rfl⟩))
      · rw [SetLike.mem_coe, hrowR]
        exact subset_span (Or.inr ⟨r.1, r.2, rfl⟩)
    · rw [span_le]
      rintro _ (⟨r, rfl⟩ | ⟨j, hj, rfl⟩)
      · have : w r = - (N2 * S).row (Sum.inl r) := by rw [hrowL, neg_neg]
        rw [SetLike.mem_coe, this]
        exact neg_mem (subset_span ⟨_, rfl⟩)
      · rw [SetLike.mem_coe, ← hrowR ⟨j, hj⟩]
        exact subset_span ⟨_, rfl⟩
  have hcard2 : Fintype.card {j // Q j} = min X m := by
    rw [Fintype.card_subtype, min_comm, ← Fin.card_filter_val_lt (n := m) (m := X)]
    exact Finset.card_bij (fun a _ => a) (by intro a ha; simpa [Q, QD] using ha)
      (fun _ _ _ _ h => h) (by intro b hb; exact ⟨b, by simpa [Q, QD] using hb, rfl⟩)
  have h4 : finrank K (span K (Set.range fun r (j : {j // ¬ Q j}) => w r j.1)) =
      (p.submatrix (fun r : {r : Fin m // r.val < Y} => r.1)
        (fun c : {c : Fin m // X ≤ c.val} => c.1)).rank := by
    refine Eq.trans (Matrix.rank_eq_finrank_span_row
      (Matrix.of fun (r : {r : Fin m // r.val < Y}) (j : {j // ¬ Q j}) => w r j.1)).symm ?_
    apply rank_eq_of_range_cols
    ext u
    constructor
    · rintro ⟨⟨c, hc⟩, rfl⟩
      exact ⟨⟨c, not_lt.1 hc⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨⟨c.1, not_lt.2 c.2⟩, rfl⟩
  rw [h1, Matrix.rank_eq_finrank_span_cols, hspan1, finrank_span_union_units, h2, h3,
    Matrix.rank_eq_finrank_span_row, hspan2, finrank_span_union_units, h4]
  omega

end PSwapAux

theorem pswap_ranks {m : ℕ} {K : Type*} [Field K] (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
    (X Y : ℕ) :
    -- (B) rows H_{<X}, columns H_{≥Y} ⊕ D
    (Matrix.of fun (r : {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun c => (1 - p) r.1 c.1) (fun c => p r.1 c) c).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val ∧ c.val < X).card +
      (p.submatrix (fun r : {r : Fin m // r.val < min X Y} => r.1) id).rank ∧
    -- (C) rows H ⊕ D_{<X}, columns D_{≥Y}
    (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val}) =>
        Sum.elim (fun r => p r c.1) (fun r => (1 - p) r.1 c.1) r).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val ∧ c.val < X).card +
      (p.submatrix id (fun c : {c : Fin m // max X Y ≤ c.val} => c.1)).rank ∧
    -- (D) rows H ⊕ D_{<X}, columns H_{≥Y} ⊕ D
    (Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun r => Sum.elim (fun c => (1 - p) r c.1) (fun c => p r c) c)
          (fun r => Sum.elim (fun c => p r.1 c.1) (fun c => (1 - p) r.1 c) c) r).rank =
      (Finset.univ.filter fun c : Fin m => Y ≤ c.val).card + min X m +
      (p.submatrix (fun r : {r : Fin m // r.val < Y} => r.1) (fun c : {c : Fin m // X ≤ c.val} => c.1)).rank :=
  ⟨PSwapAux.partB p X Y, PSwapAux.partC p X Y, PSwapAux.partD p hp X Y⟩

end Sec_PSwap

section Sec_Bruhat


open Matrix Finset

namespace BruhatAux

variable {K : Type*} [Field K] {m : ℕ}

/-- Lower triangular with nonzero diagonal. -/
def LowerND (M : Matrix (Fin m) (Fin m) K) : Prop :=
  (∀ i j, i < j → M i j = 0) ∧ ∀ i, M i i ≠ 0

lemma lowerND_one : LowerND (1 : Matrix (Fin m) (Fin m) K) :=
  ⟨fun i j h => by simp [one_apply, h.ne], fun i => by simp⟩

lemma lowerND_mul {M N : Matrix (Fin m) (Fin m) K} (hM : LowerND M) (hN : LowerND N) :
    LowerND (M * N) := by
  have diag : ∀ i, (M * N) i i = M i i * N i i := by
    intro i
    rw [mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hN.1 k i h, mul_zero]
      · rw [hM.1 i k h, zero_mul]
    · simp
  refine ⟨fun i j hij => ?_, fun i => by rw [diag]; exact mul_ne_zero (hM.2 i) (hN.2 i)⟩
  rw [mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hM.1 i k h, zero_mul]
  · rw [hN.1 k j (lt_of_le_of_lt h hij), mul_zero]

lemma isLower_of (M : Matrix (Fin m) (Fin m) K) (h : LowerND M) : M.IsLowerTriangular :=
  fun i j hij => h.1 i j hij

lemma det_ne_zero_of (M : Matrix (Fin m) (Fin m) K) (h : LowerND M) : M.det ≠ 0 := by
  rw [det_of_isLowerTriangular M (isLower_of M h)]
  exact Finset.prod_ne_zero_iff.2 fun i _ => h.2 i

lemma lowerND_inv (M : Matrix (Fin m) (Fin m) K) (h : LowerND M) : LowerND M⁻¹ := by
  have hd : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne_zero_of M h)
  have : Invertible M := invertibleOfIsUnitDet M hd
  have hl : M⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular (isLower_of M h)
  refine ⟨fun i j hij => hl hij, fun i => ?_⟩
  -- diagonal of M * M⁻¹ = 1
  have h1 : (M * M⁻¹) i i = 1 := by rw [mul_inv_of_invertible]; simp
  have h2 : (M * M⁻¹) i i = M i i * M⁻¹ i i := by
    rw [mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · rw [hl hk, mul_zero]
      · rw [h.1 i k hk, zero_mul]
    · simp
  intro h0
  rw [h2, h0, mul_zero] at h1
  exact zero_ne_one h1

/-- Rows with index `< k` are clean: zero, or a single `1` whose column is otherwise zero. -/
def Clean (B : Matrix (Fin m) (Fin m) K) (k : ℕ) : Prop :=
  ∀ i : Fin m, i.val < k → (∀ j, B i j = 0) ∨
    ∃ j, B i j = 1 ∧ (∀ j', j' ≠ j → B i j' = 0) ∧ ∀ i', i' ≠ i → B i' j = 0

lemma clean_zero (B : Matrix (Fin m) (Fin m) K) : Clean B 0 := fun i h => absurd h (Nat.not_lt_zero _)

/-- In a clean row `r < k`, the entry in any column `j` where row `k'` (with `k' ≥ k`) is nonzero vanishes. -/
lemma clean_col_zero {B : Matrix (Fin m) (Fin m) K} {k : ℕ} (hB : Clean B k) (r k' : Fin m)
    (hr : r.val < k) (hk' : k ≤ k'.val) (j : Fin m) (hj : B k' j ≠ 0) : B r j = 0 := by
  rcases hB r hr with h | ⟨σ, -, hrow, hcol⟩
  · exact h j
  · by_cases hσ : j = σ
    · subst hσ
      exact absurd (hcol k' (fun h => by subst h; omega)) hj
    · exact hrow j hσ

lemma step (B : Matrix (Fin m) (Fin m) K) (k : Fin m) (hB : Clean B k.val) :
    ∃ L R : Matrix (Fin m) (Fin m) K, LowerND L ∧ LowerND R ∧ Clean (L * B * R) (k.val + 1) := by
  classical
  by_cases hz : ∀ j, B k j = 0
  · refine ⟨1, 1, lowerND_one, lowerND_one, ?_⟩
    simp only [Matrix.one_mul, Matrix.mul_one]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact hB i h
    · left; have : i = k := Fin.ext h; subst this; exact hz
  push Not at hz
  have hne : (univ.filter fun j => B k j ≠ 0).Nonempty := by
    obtain ⟨j, hj⟩ := hz; exact ⟨j, by simp [hj]⟩
  set j0 := (univ.filter fun j => B k j ≠ 0).max' hne with hj0def
  have hj0 : B k j0 ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  have hright : ∀ j, j0 < j → B k j = 0 := by
    intro j hj
    by_contra h
    have : j ≤ j0 := Finset.le_max' _ j (by simp [h])
    exact absurd hj (not_lt.2 this)
  set b := B k j0 with hb
  -- column operations
  set N : Matrix (Fin m) (Fin m) K := Matrix.of fun a c => if a = j0 ∧ c < j0 then -(B k c / b) else 0
  set R1 : Matrix (Fin m) (Fin m) K := 1 + N
  have hR1 : LowerND R1 := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [R1, N, Matrix.add_apply, one_apply, of_apply, hij.ne, if_false, zero_add]
      rw [if_neg]; rintro ⟨rfl, h⟩; exact absurd (hij.trans h) (lt_irrefl _)
    · simp only [R1, N, Matrix.add_apply, of_apply, one_apply_eq]
      rw [if_neg (by rintro ⟨rfl, h⟩; exact lt_irrefl _ h)]; simp
  set B1 := B * R1 with hB1def
  have hB1 : ∀ r c, B1 r c = B r c + (if c < j0 then -(B k c / b) * B r j0 else 0) := by
    intro r c
    simp only [B1, R1, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    congr 1
    rw [mul_apply, Finset.sum_eq_single j0]
    · simp only [N, of_apply, true_and]
      split_ifs <;> ring
    · intro a _ ha; simp [N, ha]
    · simp
  have hB1k : ∀ c, B1 k c = if c = j0 then b else 0 := by
    intro c
    rw [hB1]
    rcases lt_trichotomy c j0 with h | h | h
    · rw [if_pos h, if_neg h.ne]; field_simp; ring
    · subst h; simp [hb]
    · rw [if_neg (not_lt.2 h.le), if_neg h.ne', hright c h, add_zero]
  -- row operations
  set M : Matrix (Fin m) (Fin m) K := Matrix.of fun r a => if a = k ∧ k < r then -(B1 r j0 / b) else 0
  set L1 : Matrix (Fin m) (Fin m) K := 1 + M
  have hL1 : LowerND L1 := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [L1, M, Matrix.add_apply, one_apply, of_apply, hij.ne, if_false, zero_add]
      rw [if_neg]; rintro ⟨rfl, h⟩; exact absurd (hij.trans h) (lt_irrefl _)
    · simp only [L1, M, Matrix.add_apply, of_apply, one_apply_eq]
      rw [if_neg (by rintro ⟨rfl, h⟩; exact lt_irrefl _ h)]; simp
  set B2 := L1 * B1 with hB2def
  have hB2 : ∀ r c, B2 r c = B1 r c + (if k < r then -(B1 r j0 / b) * B1 k c else 0) := by
    intro r c
    simp only [B2, L1, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    congr 1
    rw [mul_apply, Finset.sum_eq_single k]
    · simp only [M, of_apply, true_and]
      split_ifs <;> ring
    · intro a _ ha; simp [M, ha]
    · simp
  -- scaling
  set D : Matrix (Fin m) (Fin m) K := diagonal fun i => if i = k then b⁻¹ else 1
  have hD : LowerND D := by
    refine ⟨fun i j hij => by simp [D, diagonal_apply, hij.ne], fun i => ?_⟩
    simp only [D, diagonal_apply_eq]
    split_ifs
    · exact inv_ne_zero hj0
    · exact one_ne_zero
  refine ⟨D * L1, R1, lowerND_mul hD hL1, hR1, ?_⟩
  have hfin : D * L1 * B * R1 = D * B2 := by
    simp only [B2, B1, Matrix.mul_assoc]
  rw [hfin]
  have hDB : ∀ r c, (D * B2) r c = (if r = k then b⁻¹ else 1) * B2 r c := by
    intro r c; simp [D, diagonal_mul]
  -- clean rows below k are untouched
  have hold : ∀ r : Fin m, r.val < k.val → ∀ c, (D * B2) r c = B r c := by
    intro r hr c
    have hrk : r ≠ k := fun h => by subst h; omega
    have hkr : ¬ k < r := fun h => by rw [Fin.lt_def] at h; omega
    have hrj0 : B r j0 = 0 := clean_col_zero hB r k hr le_rfl j0 hj0
    rw [hDB, if_neg hrk, one_mul, hB2, if_neg hkr, add_zero, hB1, hrj0]
    simp
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
  · rcases hB i hi with h | ⟨σ, h1, hrow, hcol⟩
    · left; intro j; rw [hold i hi, h]
    · right
      refine ⟨σ, by rw [hold i hi, h1], fun j hj => by rw [hold i hi, hrow j hj], fun i' hi' => ?_⟩
      have hσj0 : σ ≠ j0 := by
        rintro rfl; exact hj0 (hcol k (fun h => by subst h; omega))
      have hkσ : B k σ = 0 := hcol k (fun h => by subst h; omega)
      rw [hDB, hB2, hB1k, if_neg hσj0, mul_zero]
      simp only [ite_self, add_zero]
      rw [hB1, hcol i' hi', hkσ]
      simp
  · have hik : i = k := Fin.ext hi
    subst hik
    right
    refine ⟨j0, ?_, fun j hj => ?_, fun i' hi' => ?_⟩
    · rw [hDB, if_pos rfl, hB2, if_neg (lt_irrefl _), add_zero, hB1k, if_pos rfl]
      exact inv_mul_cancel₀ hj0
    · rw [hDB, hB2, if_neg (lt_irrefl _), add_zero, hB1k, if_neg hj, mul_zero]
    · rw [hDB, if_neg hi', hB2, hB1k, if_pos rfl, one_mul]
      rcases lt_trichotomy i' i with h | h | h
      · rw [if_neg (not_lt.2 h.le), add_zero]
        have := hold i' h j0
        rw [hDB, if_neg hi', one_mul, hB2, if_neg (not_lt.2 h.le), add_zero] at this
        rw [this]
        exact clean_col_zero hB i' i h le_rfl j0 hj0
      · exact absurd h hi'
      · rw [if_pos h]; field_simp; ring

lemma reduce (A : Matrix (Fin m) (Fin m) K) :
    ∀ k ≤ m, ∃ L R : Matrix (Fin m) (Fin m) K, LowerND L ∧ LowerND R ∧ Clean (L * A * R) k := by
  intro k
  induction k with
  | zero => intro _; exact ⟨1, 1, lowerND_one, lowerND_one, clean_zero _⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, R, hL, hR, hc⟩ := ih (by omega)
    obtain ⟨L', R', hL', hR', hc'⟩ := step (L * A * R) ⟨k, by omega⟩ hc
    refine ⟨L' * L, R * R', lowerND_mul hL' hL, lowerND_mul hR hR', ?_⟩
    simpa [Matrix.mul_assoc] using hc'

end BruhatAux

open BruhatAux in
theorem bruhat_exists {m : ℕ} {K : Type*} [Field K] [DecidableEq K] (A : Matrix (Fin m) (Fin m) K) :
    ∃ E₁ P E₂ : Matrix (Fin m) (Fin m) K,
      (∀ i j, i < j → E₁ i j = 0) ∧ (∀ i, E₁ i i ≠ 0) ∧
      (∀ i j, i < j → E₂ i j = 0) ∧ (∀ i, E₂ i i ≠ 0) ∧
      (∀ i j, P i j = 0 ∨ P i j = 1) ∧
      (∀ i j j', P i j = 1 → P i j' = 1 → j = j') ∧
      (∀ i i' j, P i j = 1 → P i' j = 1 → i = i') ∧
      (Finset.univ.filter fun x : Fin m × Fin m => P x.1 x.2 = 1).card = A.rank ∧
      A = E₁ * P * E₂ := by
  classical
  obtain ⟨L, R, hL, hR, hc⟩ := reduce A m le_rfl
  set P := L * A * R with hP
  have hLd := det_ne_zero_of L hL
  have hRd := det_ne_zero_of R hR
  have : Invertible L := invertibleOfIsUnitDet L (isUnit_iff_ne_zero.2 hLd)
  have : Invertible R := invertibleOfIsUnitDet R (isUnit_iff_ne_zero.2 hRd)
  have hA : A = L⁻¹ * P * R⁻¹ := by
    simp only [hP, Matrix.mul_assoc, inv_mul_cancel_left_of_invertible]
    rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
  have hrow : ∀ i, (∀ j, P i j = 0) ∨
      ∃ j, P i j = 1 ∧ (∀ j', j' ≠ j → P i j' = 0) ∧ ∀ i', i' ≠ i → P i' j = 0 :=
    fun i => hc i i.isLt
  have h01 : ∀ i j, P i j = 0 ∨ P i j = 1 := by
    intro i j
    rcases hrow i with h | ⟨σ, h1, hr, -⟩
    · exact Or.inl (h j)
    · by_cases hj : j = σ
      · subst hj; exact Or.inr h1
      · exact Or.inl (hr j hj)
  have hrowu : ∀ i j j', P i j = 1 → P i j' = 1 → j = j' := by
    intro i j j' h h'
    rcases hrow i with hz | ⟨σ, -, hr, -⟩
    · rw [hz j] at h; exact absurd h zero_ne_one
    · by_contra hne
      by_cases hj : j = σ
      · subst hj; rw [hr j' (Ne.symm hne)] at h'; exact zero_ne_one h'
      · rw [hr j hj] at h; exact zero_ne_one h
  have hcolu : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i' := by
    intro i i' j h h'
    rcases hrow i with hz | ⟨σ, -, hr, hcl⟩
    · rw [hz j] at h; exact absurd h zero_ne_one
    · have hjσ : j = σ := by
        by_contra hj; rw [hr j hj] at h; exact zero_ne_one h
      subst hjσ
      by_contra hne
      rw [hcl i' (Ne.symm hne)] at h'; exact zero_ne_one h'
  -- rank count
  have hrankP : P.rank = A.rank := by
    rw [hP, rank_mul_eq_left_of_isUnit_det R _ (isUnit_iff_ne_zero.2 hRd),
      rank_mul_eq_right_of_isUnit_det L A (isUnit_iff_ne_zero.2 hLd)]
  have hPPt : P * Pᵀ = diagonal fun i => if ∃ j, P i j = 1 then (1 : K) else 0 := by
    ext i i'
    rw [mul_apply, diagonal_apply]
    simp only [transpose_apply]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl]
      split_ifs with hex
      · obtain ⟨j, hj⟩ := hex
        rw [Finset.sum_eq_single j]
        · rw [hj, one_mul]
        · intro j' _ hj'
          rcases h01 i j' with h | h
          · rw [h, zero_mul]
          · exact absurd (hrowu i j j' hj h).symm hj'
        · simp
      · push Not at hex
        refine Finset.sum_eq_zero fun j _ => ?_
        rcases h01 i j with h | h
        · rw [h, zero_mul]
        · exact absurd h (hex j)
    · rw [if_neg hii]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h01 i j with h | h
      · rw [h, zero_mul]
      rcases h01 i' j with h' | h'
      · rw [h', mul_zero]
      · exact absurd (hcolu i i' j h h') hii
  have hPPtP : P * Pᵀ * P = P := by
    rw [hPPt]
    ext i j
    rw [diagonal_mul]
    split_ifs with hex
    · rw [one_mul]
    · push Not at hex
      rw [zero_mul]
      rcases h01 i j with h | h
      · exact h.symm
      · exact absurd h (hex j)
  have hrank1 : P.rank = (P * Pᵀ).rank := by
    apply le_antisymm
    · calc P.rank = (P * Pᵀ * P).rank := by rw [hPPtP]
        _ ≤ (P * Pᵀ).rank := rank_mul_le_left _ _
    · exact rank_mul_le_left _ _
  have hrank2 : (P * Pᵀ).rank = (univ.filter fun i => ∃ j, P i j = 1).card := by
    rw [hPPt, rank_diagonal, Fintype.card_subtype]
    congr 1
    ext i; simp
  have hcount : (univ.filter fun x : Fin m × Fin m => P x.1 x.2 = 1).card =
      (univ.filter fun i => ∃ j, P i j = 1).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨x.2, hx⟩
    · intro x hx y hy hxy
      simp only [mem_filter, mem_univ, true_and] at hx hy
      have h2 : x.2 = y.2 := hrowu x.1 x.2 y.2 hx (hxy ▸ hy)
      exact Prod.ext hxy h2
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      obtain ⟨j, hj⟩ := hi
      exact ⟨(i, j), by simp [hj], rfl⟩
  have hLi := lowerND_inv L hL
  have hRi := lowerND_inv R hR
  exact ⟨L⁻¹, P, R⁻¹, hLi.1, hLi.2, hRi.1, hRi.2, h01, hrowu, hcolu,
    by rw [hcount, ← hrank2, ← hrank1, hrankP], hA⟩

end Sec_Bruhat

section Sec_BruhatRank


open Matrix Finset

namespace BruhatRankAux

variable {K : Type*} [Field K] {m : ℕ}

/-- Rank of a rectangular 0/1 matrix with at most one `1` per row and column = number of ones. -/
lemma rank_pp {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [DecidableEq K]
    (P : Matrix ι κ K)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1)
    (hrow : ∀ i j j', P i j = 1 → P i j' = 1 → j = j')
    (hcol : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i') :
    P.rank = (univ.filter fun x : ι × κ => P x.1 x.2 = 1).card := by
  have hPPt : P * Pᵀ = diagonal fun i => if ∃ j, P i j = 1 then (1 : K) else 0 := by
    ext i i'
    rw [mul_apply, diagonal_apply]
    simp only [transpose_apply]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl]
      split_ifs with hex
      · obtain ⟨j, hj⟩ := hex
        rw [Finset.sum_eq_single j]
        · rw [hj, one_mul]
        · intro j' _ hj'
          rcases h01 i j' with h | h
          · rw [h, zero_mul]
          · exact absurd (hrow i j j' hj h).symm hj'
        · simp
      · push Not at hex
        refine Finset.sum_eq_zero fun j _ => ?_
        rcases h01 i j with h | h
        · rw [h, zero_mul]
        · exact absurd h (hex j)
    · rw [if_neg hii]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h01 i j with h | h
      · rw [h, zero_mul]
      rcases h01 i' j with h' | h'
      · rw [h', mul_zero]
      · exact absurd (hcol i i' j h h') hii
  have hPPtP : P * Pᵀ * P = P := by
    rw [hPPt]
    ext i j
    rw [diagonal_mul]
    split_ifs with hex
    · rw [one_mul]
    · push Not at hex
      rw [zero_mul]
      rcases h01 i j with h | h
      · exact h.symm
      · exact absurd h (hex j)
  have hrank1 : P.rank = (P * Pᵀ).rank := by
    apply le_antisymm
    · calc P.rank = (P * Pᵀ * P).rank := by rw [hPPtP]
        _ ≤ (P * Pᵀ).rank := rank_mul_le_left _ _
    · exact rank_mul_le_left _ _
  rw [hrank1, hPPt, rank_diagonal, Fintype.card_subtype]
  refine (Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_).symm
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    exact ⟨x.2, hx⟩
  · intro x hx y hy hxy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    exact Prod.ext hxy (hrow x.1 x.2 y.2 hx (hxy ▸ hy))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff, one_ne_zero,
      imp_false, not_not] at hi
    obtain ⟨j, hj⟩ := hi
    exact ⟨(i, j), by simp [hj], rfl⟩

lemma sum_sub {p : Fin m → Prop} [DecidablePred p] (f : Fin m → K) (hf : ∀ a, ¬ p a → f a = 0) :
    ∑ a, f a = ∑ a : {a // p a}, f a.1 := by
  rw [← Finset.sum_subtype (univ.filter p) (by simp) f, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rfl
  · exact hf a h

end BruhatRankAux

open BruhatRankAux in
theorem bruhat_rank {m : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (E₁ P E₂ : Matrix (Fin m) (Fin m) K)
    (hE₁ : ∀ i j, i < j → E₁ i j = 0) (hd₁ : ∀ i, E₁ i i ≠ 0)
    (hE₂ : ∀ i j, i < j → E₂ i j = 0) (hd₂ : ∀ i, E₂ i i ≠ 0)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1)
    (hrow : ∀ i j j', P i j = 1 → P i j' = 1 → j = j')
    (hcol : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i') (i j : Fin m) :
    ((E₁ * P * E₂).submatrix (fun r : {r : Fin m // r ≤ i} => r.1)
        (fun c : {c : Fin m // j ≤ c} => c.1)).rank =
      (univ.filter fun x : Fin m × Fin m => x.1 ≤ i ∧ j ≤ x.2 ∧ P x.1 x.2 = 1).card := by
  classical
  have hfac : (E₁ * P * E₂).submatrix (fun r : {r : Fin m // r ≤ i} => r.1)
        (fun c : {c : Fin m // j ≤ c} => c.1) =
      E₁.submatrix (fun r : {r : Fin m // r ≤ i} => r.1) (fun r : {r : Fin m // r ≤ i} => r.1) *
        P.submatrix (fun r : {r : Fin m // r ≤ i} => r.1) (fun c : {c : Fin m // j ≤ c} => c.1) *
        E₂.submatrix (fun c : {c : Fin m // j ≤ c} => c.1) (fun c : {c : Fin m // j ≤ c} => c.1) := by
    ext r c
    simp only [submatrix_apply, mul_apply]
    rw [sum_sub (p := fun b => j ≤ b) (fun b => (∑ a, E₁ r.1 a * P a b) * E₂ b c.1)
      (fun b hb => by rw [hE₂ b c.1 (lt_of_lt_of_le (not_le.1 hb) c.2), mul_zero])]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact sum_sub (p := fun a => a ≤ i) (fun a => E₁ r.1 a * P a b.1)
      (fun a ha => by rw [hE₁ r.1 a (lt_of_le_of_lt r.2 (not_le.1 ha)), zero_mul])
  have hdet : ∀ (p : Fin m → Prop) [DecidablePred p] (E : Matrix (Fin m) (Fin m) K),
      (∀ i j, i < j → E i j = 0) → (∀ i, E i i ≠ 0) →
      IsUnit (E.submatrix (fun r : {r // p r} => r.1) (fun r : {r // p r} => r.1)).det := by
    intro p _ E hE hd
    have hl : (E.submatrix (fun r : {r // p r} => r.1) (fun r : {r // p r} => r.1)).IsLowerTriangular :=
      fun a b hab => hE _ _ (show a.1 < b.1 from hab)
    rw [det_of_isLowerTriangular _ hl, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hd a.1
  rw [hfac, rank_mul_eq_left_of_isUnit_det _ _ (hdet (fun c => j ≤ c) E₂ hE₂ hd₂),
    rank_mul_eq_right_of_isUnit_det _ _ (hdet (fun r => r ≤ i) E₁ hE₁ hd₁)]
  rw [rank_pp (P.submatrix (fun r : {r : Fin m // r ≤ i} => r.1) (fun c : {c : Fin m // j ≤ c} => c.1)) (fun a b => h01 _ _) (fun a b b' h h' => Subtype.ext (hrow _ _ _ h h'))
    (fun a a' b h h' => Subtype.ext (hcol _ _ _ h h'))]
  refine Finset.card_bij (fun x _ => (x.1.1, x.2.1)) ?_ ?_ ?_
  · intro x hx
    have hx' : P x.1.1 x.2.1 = 1 := (Finset.mem_filter.1 hx).2
    simpa using ⟨x.1.2, x.2.2, hx'⟩
  · intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (Subtype.ext hxy.1) (Subtype.ext hxy.2)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    refine ⟨(⟨x.1, hx.1⟩, ⟨x.2, hx.2.1⟩), ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hx.2.2⟩

end Sec_BruhatRank

section Sec_PPUniq


open Finset

namespace PPUniqAux

variable {n : ℕ} {K : Type*} [One K] [DecidableEq K]

/-- Number of ones of `P` in rows `< X` and columns `≥ Y`. -/
def cnt (P : Matrix (Fin n) (Fin n) K) (X Y : ℕ) : ℕ :=
  (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card

lemma cnt_succ_row (P : Matrix (Fin n) (Fin n) K) (X Y : ℕ) :
    cnt P (X + 1) Y = cnt P X Y +
      (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hP : P x.1 x.2 = 1 <;> simp [hP] <;> omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    obtain ⟨a1, a2, -⟩ := h1
    obtain ⟨b1, b2, -⟩ := h2
    omega

lemma row_succ_col (P : Matrix (Fin n) (Fin n) K) (X Y : ℕ) :
    (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card =
      (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ x.2.val = Y ∧ P x.1 x.2 = 1).card +
      (univ.filter fun x : Fin n × Fin n => x.1.val = X ∧ Y + 1 ≤ x.2.val ∧ P x.1 x.2 = 1).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hP : P x.1 x.2 = 1 <;> simp [hP] <;> omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    obtain ⟨a1, a2, -⟩ := h1
    obtain ⟨b1, b2, -⟩ := h2
    omega

lemma single_cnt (P : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (univ.filter fun x : Fin n × Fin n => x.1.val = i.val ∧ x.2.val = j.val ∧ P x.1 x.2 = 1).card =
      if P i j = 1 then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(i, j), ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · rintro rfl; exact ⟨rfl, rfl, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2, h3⟩
    have : x = (i, j) := Prod.ext (Fin.ext h1) (Fin.ext h2)
    subst this
    exact h h3

end PPUniqAux

open PPUniqAux in
theorem pp_uniq {n : ℕ} {K : Type*} [Zero K] [One K] [DecidableEq K]
    (P P' : Matrix (Fin n) (Fin n) K)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1) (h01' : ∀ i j, P' i j = 0 ∨ P' i j = 1)
    (h : ∀ X Y : ℕ,
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card =
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P' x.1 x.2 = 1).card) :
    P = P' := by
  have hc : ∀ X Y, cnt P X Y = cnt P' X Y := h
  have key : ∀ i j : Fin n, (if P i j = 1 then 1 else 0) = (if P' i j = 1 then 1 else 0) := by
    intro i j
    rw [← single_cnt P i j, ← single_cnt P' i j]
    have e1 := cnt_succ_row P i.val j.val
    have e2 := cnt_succ_row P' i.val j.val
    have e3 := row_succ_col P i.val j.val
    have e4 := row_succ_col P' i.val j.val
    have e5 := cnt_succ_row P i.val (j.val + 1)
    have e6 := cnt_succ_row P' i.val (j.val + 1)
    rw [hc, hc] at e1
    rw [hc, hc] at e5
    omega
  ext i j
  have := key i j
  rcases h01 i j with a | a <;> rcases h01' i j with b | b <;> rw [a, b] at this ⊢
  all_goals (simp at this; first | exact this | exact this.symm)

end Sec_PPUniq

section Sec_Runs

open Matrix Finset

namespace RunsAux

variable {K : Type*} [Field K]

lemma rank_submatrix_range {ι κ α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix ι κ K) (f : α → ι) (f' : β → ι) (g : γ → κ) (g' : δ → κ)
    (hf : Set.range f = Set.range f') (hg : Set.range g = Set.range g') :
    (A.submatrix f g).rank = (A.submatrix f' g').rank := by
  trans (A.submatrix f' g).rank
  · apply PSwapAux.rank_eq_of_range_rows
    have h1 : (A.submatrix f g).row = (fun i c => A i (g c)) ∘ f := rfl
    have h2 : (A.submatrix f' g).row = (fun i c => A i (g c)) ∘ f' := rfl
    rw [h1, h2, Set.range_comp, Set.range_comp, hf]
  · apply PSwapAux.rank_eq_of_range_cols
    have h1 : (A.submatrix f' g).col = (fun j r => A (f' r) j) ∘ g := rfl
    have h2 : (A.submatrix f' g').col = (fun j r => A (f' r) j) ∘ g' := rfl
    rw [h1, h2, Set.range_comp, Set.range_comp, hg]

lemma bruhat_rank_nat {n : ℕ} [DecidableEq K] (E₁ P E₂ : Matrix (Fin n) (Fin n) K)
    (hE₁ : ∀ i j, i < j → E₁ i j = 0) (hd₁ : ∀ i, E₁ i i ≠ 0)
    (hE₂ : ∀ i j, i < j → E₂ i j = 0) (hd₂ : ∀ i, E₂ i i ≠ 0)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1)
    (hrow : ∀ i j j', P i j = 1 → P i j' = 1 → j = j')
    (hcol : ∀ i i' j, P i j = 1 → P i' j = 1 → i = i') (X Y : ℕ) :
    ((E₁ * P * E₂).submatrix (fun r : {r : Fin n // r.val < X} => r.1)
        (fun c : {c : Fin n // Y ≤ c.val} => c.1)).rank =
      (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX
    have : (univ.filter fun x : Fin n × Fin n => x.1.val < 0 ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card
        = 0 := by simp
    rw [this]
    apply Nat.eq_zero_of_le_zero
    refine (Matrix.rank_le_card_height _).trans ?_
    simp
  by_cases hY : n ≤ Y
  · have : (univ.filter fun x : Fin n × Fin n => x.1.val < X ∧ Y ≤ x.2.val ∧ P x.1 x.2 = 1).card
        = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨-, h, -⟩
      have := x.2.isLt
      omega
    rw [this]
    apply Nat.eq_zero_of_le_zero
    refine (Matrix.rank_le_card_width _).trans ?_
    rw [Nat.le_zero, Fintype.card_eq_zero_iff]
    exact ⟨fun c => by have := c.1.isLt; have := c.2; omega⟩
  push Not at hY
  let i : Fin n := ⟨min X n - 1, by omega⟩
  let j : Fin n := ⟨Y, hY⟩
  have hr : ∀ r : Fin n, r.val < X ↔ r ≤ i := fun r => by
    rw [Fin.le_iff_val_le_val]; have := r.isLt; simp only [i]; omega
  have hc : ∀ c : Fin n, Y ≤ c.val ↔ j ≤ c := fun c => by
    rw [Fin.le_iff_val_le_val]
  have heq : (E₁ * P * E₂).submatrix (fun r : {r : Fin n // r.val < X} => r.1)
        (fun c : {c : Fin n // Y ≤ c.val} => c.1) =
      ((E₁ * P * E₂).submatrix (fun r : {r : Fin n // r ≤ i} => r.1)
        (fun c : {c : Fin n // j ≤ c} => c.1)).submatrix (Equiv.subtypeEquivRight hr)
        (Equiv.subtypeEquivRight hc) := rfl
  rw [heq, Matrix.rank_submatrix, bruhat_rank E₁ P E₂ hE₁ hd₁ hE₂ hd₂ h01 hrow hcol i j]
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [hr, hc]


section Counts

variable {m : ℕ} [DecidableEq K] (π : Matrix (Fin m) (Fin m) K)

def ds (q : Fin m → Fin m → Prop) [∀ i j, Decidable (q i j)] : ℕ :=
  ∑ i, ∑ j, if q i j ∧ π i j = 1 then 1 else 0

def ss (q : Fin m → Prop) [DecidablePred q] : ℕ := ∑ i, if q i then 1 else 0

def sE (q : Fin m → Prop) [DecidablePred q] : ℕ :=
  ∑ i, if q i ∧ ¬ ∃ j, π i j = 1 then 1 else 0

def sC (q : Fin m → Prop) [DecidablePred q] : ℕ :=
  ∑ j, if q j ∧ ¬ ∃ i, π i j = 1 then 1 else 0

lemma ds_eq_card (q : Fin m → Fin m → Prop) [∀ i j, Decidable (q i j)] :
    (univ.filter fun x : Fin m × Fin m => q x.1 x.2 ∧ π x.1 x.2 = 1).card = ds π q := by
  rw [card_filter, ← univ_product_univ, sum_product]; rfl

lemma ss_eq_card (q : Fin m → Prop) [DecidablePred q] :
    (univ.filter q).card = ss q := by
  rw [card_filter]; rfl

lemma ss_lt (a : ℕ) : ss (fun j : Fin m => j.val < a) = min a m := by
  rw [← ss_eq_card, Fin.card_filter_val_lt, min_comm]

lemma ss_false : ss (fun _ : Fin m => False) = 0 := by simp [ss]

lemma ds_lin {q1 q2 q3 q4 q5 : Fin m → Fin m → Prop} [∀ i j, Decidable (q1 i j)]
    [∀ i j, Decidable (q2 i j)] [∀ i j, Decidable (q3 i j)] [∀ i j, Decidable (q4 i j)]
    [∀ i j, Decidable (q5 i j)]
    (h : ∀ i j, (if q1 i j then 1 else 0) + (if q2 i j then 1 else 0) =
      (if q3 i j then 1 else 0) + (if q4 i j then 1 else 0) + (if q5 i j then (1 : ℕ) else 0)) :
    ds π q1 + ds π q2 = ds π q3 + ds π q4 + ds π q5 := by
  simp only [ds, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have := h i j
  by_cases ho : π i j = 1 <;> simp only [ho, and_true, and_false, if_false] <;> omega

lemma ss_lin {q1 q2 q3 q4 : Fin m → Prop} [DecidablePred q1] [DecidablePred q2]
    [DecidablePred q3] [DecidablePred q4]
    (h : ∀ i, (if q1 i then 1 else 0) + (if q2 i then 1 else 0) =
      (if q3 i then 1 else 0) + (if q4 i then (1 : ℕ) else 0)) :
    ss q1 + ss q2 = ss q3 + ss q4 := by
  simp only [ss, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => h i

variable {π}

lemma sum_ite_unique (t : Fin m → Prop) [DecidablePred t] (h : ∀ j j', t j → t j' → j = j') :
    (∑ j, if t j then 1 else 0) = if ∃ j, t j then 1 else 0 := by
  by_cases hex : ∃ j, t j
  · obtain ⟨j0, hj0⟩ := hex
    rw [if_pos ⟨j0, hj0⟩, sum_eq_single j0]
    · rw [if_pos hj0]
    · intro j _ hj; rw [if_neg]; exact fun ht => hj (h j j0 ht hj0)
    · simp
  · rw [if_neg hex]
    exact sum_eq_zero fun j _ => if_neg fun ht => hex ⟨j, ht⟩

lemma rowE (hrow : ∀ i j j', π i j = 1 → π i j' = 1 → j = j')
    (q : Fin m → Prop) [DecidablePred q] :
    sE π q + ds π (fun i _ => q i) = ss q := by
  simp only [sE, ds, ss, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_ite_unique (fun j => q i ∧ π i j = 1)
    (fun j j' h h' => hrow i j j' h.2 h'.2)]
  by_cases hq : q i <;> by_cases he : ∃ j, π i j = 1 <;> simp [hq, he]

lemma colE (hcol : ∀ i i' j, π i j = 1 → π i' j = 1 → i = i')
    (q : Fin m → Prop) [DecidablePred q] :
    sC π q + ds π (fun _ j => q j) = ss q := by
  simp only [sC, ds, ss]
  rw [sum_comm, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_ite_unique (fun i => q j ∧ π i j = 1)
    (fun i i' h h' => hcol i i' j h.2 h'.2)]
  by_cases hq : q j <;> by_cases he : ∃ i, π i j = 1 <;> simp [hq, he]

end Counts


section Blocks

variable {m : ℕ}

def Smat (p : Matrix (Fin m) (Fin m) K) : Matrix (Fin (m + m)) (Fin (m + m)) K :=
  (Matrix.fromBlocks (1 - p) p p (1 - p)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def Wmat [DecidableEq K] (π : Matrix (Fin m) (Fin m) K) : Matrix (Fin (m + m)) (Fin (m + m)) K :=
  (Matrix.fromBlocks
    (Matrix.diagonal fun i => if ∃ j, π i j = 1 then (0 : K) else 1) π πᵀ
    (Matrix.diagonal fun j => if ∃ i, π i j = 1 then (0 : K) else 1)).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm

lemma W_split [DecidableEq K] (π : Matrix (Fin m) (Fin m) K) (X Y : ℕ) :
    (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card =
      sE π (fun i => i.val < X ∧ Y ≤ i.val) + ds π (fun i j => i.val < X ∧ Y ≤ m + j.val) +
        ds π (fun i j => m + j.val < X ∧ Y ≤ i.val) +
        sC π (fun j => m + j.val < X ∧ Y ≤ m + j.val) := by
  rw [card_filter, ← univ_product_univ, sum_product, Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, sum_add_distrib, Wmat, submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Fin.coe_castAdd, Fin.coe_natAdd,
    transpose_apply]
  simp only [add_assoc]
  refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_))
  · simp only [sE, and_assoc]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · by_cases he : ∃ j, π i j = 1 <;> simp [he]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · simp only [ds, and_assoc]
  · simp only [ds, and_assoc]; rw [sum_comm]
  · simp only [sC, and_assoc]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · by_cases he : ∃ j, π j i = 1 <;> simp [he]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

def rowLo (X : ℕ) : {r : Fin m // r.val < X} → Fin (m + m) := fun r => finSumFinEquiv (Sum.inl r.1)
def rowHi (x : ℕ) : Fin m ⊕ {r : Fin m // r.val < x} → Fin (m + m) :=
  Sum.elim (fun r => finSumFinEquiv (Sum.inl r)) (fun r => finSumFinEquiv (Sum.inr r.1))
def colLo (Y : ℕ) : {c : Fin m // Y ≤ c.val} ⊕ Fin m → Fin (m + m) :=
  Sum.elim (fun c => finSumFinEquiv (Sum.inl c.1)) (fun c => finSumFinEquiv (Sum.inr c))
def colHi (y : ℕ) : {c : Fin m // y ≤ c.val} → Fin (m + m) := fun c => finSumFinEquiv (Sum.inr c.1)

lemma range_rowLo (X : ℕ) (hX : X ≤ m) :
    Set.range (rowLo (m := m) X) = Set.range (fun r : {r : Fin (m + m) // r.val < X} => r.1) := by
  ext k
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨_, by simp [rowLo, r.2]⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨⟨⟨k.val, by omega⟩, hk⟩, Fin.ext (by simp [rowLo])⟩

lemma range_rowHi (X : ℕ) (hX : m ≤ X) :
    Set.range (rowHi (m := m) (X - m)) =
      Set.range (fun r : {r : Fin (m + m) // r.val < X} => r.1) := by
  ext k
  constructor
  · rintro ⟨r | r, rfl⟩
    · exact ⟨⟨_, by simp [rowHi]; omega⟩, rfl⟩
    · exact ⟨⟨_, by simp [rowHi]; omega⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    by_cases hkm : k.val < m
    · exact ⟨Sum.inl ⟨k.val, hkm⟩, Fin.ext (by simp [rowHi])⟩
    · exact ⟨Sum.inr ⟨⟨k.val - m, by omega⟩, by simp; omega⟩, Fin.ext (by simp [rowHi]; omega)⟩

lemma range_colLo (Y : ℕ) (hY : Y ≤ m) :
    Set.range (colLo (m := m) Y) = Set.range (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1) := by
  ext k
  constructor
  · rintro ⟨c | c, rfl⟩
    · exact ⟨⟨_, by simp [colLo]; omega⟩, rfl⟩
    · exact ⟨⟨_, by simp [colLo]; omega⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    by_cases hkm : k.val < m
    · exact ⟨Sum.inl ⟨⟨k.val, hkm⟩, hk⟩, Fin.ext (by simp [colLo])⟩
    · exact ⟨Sum.inr ⟨k.val - m, by omega⟩, Fin.ext (by simp [colLo]; omega)⟩

lemma range_colHi (Y : ℕ) (hY : m ≤ Y) :
    Set.range (colHi (m := m) (Y - m)) =
      Set.range (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1) := by
  ext k
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨_, by simp [colHi]; have := c.2; omega⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨⟨⟨k.val - m, by omega⟩, by simp; omega⟩, Fin.ext (by simp [colHi]; omega)⟩

end Blocks


section Cases

variable {m : ℕ} [DecidableEq K]

lemma p_rank (p F₁ π F₂ : Matrix (Fin m) (Fin m) K)
    (hF₁ : ∀ i j, i < j → F₁ i j = 0) (hd₁ : ∀ i, F₁ i i ≠ 0)
    (hF₂ : ∀ i j, i < j → F₂ i j = 0) (hd₂ : ∀ i, F₂ i i ≠ 0)
    (h01 : ∀ i j, π i j = 0 ∨ π i j = 1)
    (hrow : ∀ i j j', π i j = 1 → π i j' = 1 → j = j')
    (hcol : ∀ i i' j, π i j = 1 → π i' j = 1 → i = i')
    (hfac : p = F₁ * π * F₂) (a b : ℕ) :
    (p.submatrix (fun r : {r : Fin m // r.val < a} => r.1)
      (fun c : {c : Fin m // b ≤ c.val} => c.1)).rank =
      ds π (fun i j => i.val < a ∧ b ≤ j.val) := by
  subst hfac
  rw [bruhat_rank_nat F₁ π F₂ hF₁ hd₁ hF₂ hd₂ h01 hrow hcol, ← ds_eq_card]
  congr 1
  apply filter_congr
  intro x _
  simp only [and_assoc]

lemma assemble {π : Matrix (Fin m) (Fin m) K}
    (hrow : ∀ i j j', π i j = 1 → π i j' = 1 → j = j')
    (hcol : ∀ i i' j, π i j = 1 → π i' j = 1 → i = i') (X Y R : ℕ)
    (Rs1 Rs2 : Fin m → Prop) [DecidablePred Rs1] [DecidablePred Rs2]
    (Rd : Fin m → Fin m → Prop) [∀ i j, Decidable (Rd i j)]
    (hs : ss (fun i : Fin m => i.val < X ∧ Y ≤ i.val) +
        ss (fun j : Fin m => m + j.val < X ∧ Y ≤ m + j.val) = ss Rs1 + ss Rs2)
    (hd : ds π (fun i j => i.val < X ∧ Y ≤ m + j.val) +
        ds π (fun i j => m + j.val < X ∧ Y ≤ i.val) =
        ds π Rd + ds π (fun i (_ : Fin m) => i.val < X ∧ Y ≤ i.val) +
        ds π (fun (_ : Fin m) j => m + j.val < X ∧ Y ≤ m + j.val))
    (hR : R = ss Rs1 + ss Rs2 + ds π Rd) :
    R = (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card := by
  rw [W_split]
  have h1 : sE π (fun i : Fin m => i.val < X ∧ Y ≤ i.val) +
      ds π (fun i (_ : Fin m) => i.val < X ∧ Y ≤ i.val) =
      ss (fun i : Fin m => i.val < X ∧ Y ≤ i.val) := rowE hrow _
  have h2 : sC π (fun j : Fin m => m + j.val < X ∧ Y ≤ m + j.val) +
      ds π (fun (_ : Fin m) j => m + j.val < X ∧ Y ≤ m + j.val) =
      ss (fun j : Fin m => m + j.val < X ∧ Y ≤ m + j.val) := colE hcol _
  omega

variable (p : Matrix (Fin m) (Fin m) K) (π : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
  (hrow : ∀ i j j', π i j = 1 → π i j' = 1 → j = j')
  (hcol : ∀ i i' j, π i j = 1 → π i' j = 1 → i = i')
  (hpr : ∀ a b : ℕ, (p.submatrix (fun r : {r : Fin m // r.val < a} => r.1)
      (fun c : {c : Fin m // b ≤ c.val} => c.1)).rank =
      ds π (fun i j => i.val < a ∧ b ≤ j.val))
include hp hrow hcol hpr

lemma caseA (X Y : ℕ) (hX : X ≤ m) (hY : m ≤ Y) :
    ((Smat p).submatrix (fun r : {r : Fin (m + m) // r.val < X} => r.1)
      (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1)).rank =
    (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card := by
  rw [← rank_submatrix_range (Smat p) (rowLo X) _ (colHi (Y - m)) _ (range_rowLo X hX)
    (range_colHi Y hY)]
  have hm : (Smat p).submatrix (rowLo X) (colHi (Y - m)) =
      p.submatrix (fun r : {r : Fin m // r.val < X} => r.1)
        (fun c : {c : Fin m // Y - m ≤ c.val} => c.1) := by
    ext r c; simp only [Smat, rowLo, colHi, submatrix_apply, Equiv.symm_apply_apply, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  rw [hm]
  refine assemble hrow hcol X Y _ (fun _ => False) (fun _ => False)
    (fun i j => i.val < X ∧ Y - m ≤ j.val) ?_ ?_ ?_
  · exact ss_lin (fun i => by have := i.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · exact ds_lin π (fun i j => by have := i.isLt; have := j.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · rw [hpr, ss_false]; simp

lemma caseB (X Y : ℕ) (hX : X ≤ m) (hY : Y ≤ m) :
    ((Smat p).submatrix (fun r : {r : Fin (m + m) // r.val < X} => r.1)
      (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1)).rank =
    (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card := by
  rw [← rank_submatrix_range (Smat p) (rowLo X) _ (colLo Y) _ (range_rowLo X hX)
    (range_colLo Y hY)]
  have hm : (Smat p).submatrix (rowLo X) (colLo Y) =
      Matrix.of fun (r : {r : Fin m // r.val < X}) (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun c => (1 - p) r.1 c.1) (fun c => p r.1 c) c := by
    ext r (c | c) <;> simp only [Smat, rowLo, colLo, submatrix_apply, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hid : (p.submatrix (fun r : {r : Fin m // r.val < min X Y} => r.1) id).rank =
      (p.submatrix (fun r : {r : Fin m // r.val < min X Y} => r.1)
        (fun c : {c : Fin m // 0 ≤ c.val} => c.1)).rank :=
    rank_submatrix_range _ _ _ _ _ rfl (by ext; simp)
  rw [hm, (pswap_ranks p hp X Y).1, ss_eq_card, hid, hpr]
  refine assemble hrow hcol X Y _ (fun c => Y ≤ c.val ∧ c.val < X) (fun _ => False)
    (fun i j => i.val < min X Y ∧ 0 ≤ j.val) ?_ ?_ ?_
  · exact ss_lin (fun i => by have := i.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · exact ds_lin π (fun i j => by have := i.isLt; have := j.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · rw [ss_false, add_zero]

lemma caseC (X Y : ℕ) (hX : m ≤ X) (hY : m ≤ Y) :
    ((Smat p).submatrix (fun r : {r : Fin (m + m) // r.val < X} => r.1)
      (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1)).rank =
    (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card := by
  rw [← rank_submatrix_range (Smat p) (rowHi (X - m)) _ (colHi (Y - m)) _ (range_rowHi X hX)
    (range_colHi Y hY)]
  have hm : (Smat p).submatrix (rowHi (X - m)) (colHi (Y - m)) =
      Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X - m}) (c : {c : Fin m // Y - m ≤ c.val}) =>
        Sum.elim (fun r => p r c.1) (fun r => (1 - p) r.1 c.1) r := by
    ext (r | r) c <;> simp only [Smat, rowHi, colHi, submatrix_apply, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  have hid : (p.submatrix id (fun c : {c : Fin m // max (X - m) (Y - m) ≤ c.val} => c.1)).rank =
      (p.submatrix (fun r : {r : Fin m // r.val < m} => r.1)
        (fun c : {c : Fin m // max (X - m) (Y - m) ≤ c.val} => c.1)).rank :=
    rank_submatrix_range _ _ _ _ _ (by ext r; simp) rfl
  rw [hm, (pswap_ranks p hp (X - m) (Y - m)).2.1, ss_eq_card, hid, hpr]
  refine assemble hrow hcol X Y _ (fun c => Y - m ≤ c.val ∧ c.val < X - m) (fun _ => False)
    (fun i j => i.val < m ∧ max (X - m) (Y - m) ≤ j.val) ?_ ?_ ?_
  · exact ss_lin (fun i => by have := i.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · exact ds_lin π (fun i j => by have := i.isLt; have := j.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · rw [ss_false, add_zero]

lemma caseD (X Y : ℕ) (hX : m ≤ X) (hY : Y ≤ m) :
    ((Smat p).submatrix (fun r : {r : Fin (m + m) // r.val < X} => r.1)
      (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1)).rank =
    (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card := by
  rw [← rank_submatrix_range (Smat p) (rowHi (X - m)) _ (colLo Y) _ (range_rowHi X hX)
    (range_colLo Y hY)]
  have hm : (Smat p).submatrix (rowHi (X - m)) (colLo Y) =
      Matrix.of fun (r : Fin m ⊕ {r : Fin m // r.val < X - m})
        (c : {c : Fin m // Y ≤ c.val} ⊕ Fin m) =>
        Sum.elim (fun r => Sum.elim (fun c => (1 - p) r c.1) (fun c => p r c) c)
          (fun r => Sum.elim (fun c => p r.1 c.1) (fun c => (1 - p) r.1 c) c) r := by
    ext (r | r) (c | c) <;> simp only [Smat, rowHi, colLo, submatrix_apply, Sum.elim_inl, Sum.elim_inr, Equiv.symm_apply_apply, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  rw [hm, (pswap_ranks p hp (X - m) Y).2.2, ss_eq_card, ← ss_lt, hpr]
  refine assemble hrow hcol X Y _ (fun c => Y ≤ c.val) (fun c => c.val < X - m)
    (fun i j => i.val < Y ∧ X - m ≤ j.val) ?_ ?_ ?_
  · exact ss_lin (fun i => by have := i.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · exact ds_lin π (fun i j => by have := i.isLt; have := j.isLt; (try dsimp only); split_ifs <;> first | omega | contradiction)
  · rfl

lemma corner (X Y : ℕ) :
    ((Smat p).submatrix (fun r : {r : Fin (m + m) // r.val < X} => r.1)
      (fun c : {c : Fin (m + m) // Y ≤ c.val} => c.1)).rank =
    (univ.filter fun x : Fin (m + m) × Fin (m + m) =>
        x.1.val < X ∧ Y ≤ x.2.val ∧ Wmat π x.1 x.2 = 1).card := by
  rcases le_total X m with hX | hX <;> rcases le_total Y m with hY | hY
  · exact caseB p π hp hrow hcol hpr X Y hX hY
  · exact caseA p π hp hrow hcol hpr X Y hX hY
  · exact caseD p π hp hrow hcol hpr X Y hX hY
  · exact caseC p π hp hrow hcol hpr X Y hX hY

end Cases

end RunsAux

end Sec_Runs

open Matrix RunsAux in
theorem solution {m : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (p F₁ π F₂ : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
    (hF₁ : ∀ i j, i < j → F₁ i j = 0) (hd₁ : ∀ i, F₁ i i ≠ 0)
    (hF₂ : ∀ i j, i < j → F₂ i j = 0) (hd₂ : ∀ i, F₂ i i ≠ 0)
    (h01 : ∀ i j, π i j = 0 ∨ π i j = 1)
    (hrow : ∀ i j j', π i j = 1 → π i j' = 1 → j = j')
    (hcol : ∀ i i' j, π i j = 1 → π i' j = 1 → i = i')
    (hfac : p = F₁ * π * F₂) :
    ∃ E₁ E₂ : Matrix (Fin (m + m)) (Fin (m + m)) K,
      (∀ i j, i < j → E₁ i j = 0) ∧ (∀ i, E₁ i i ≠ 0) ∧
      (∀ i j, i < j → E₂ i j = 0) ∧ (∀ i, E₂ i i ≠ 0) ∧
      (Matrix.fromBlocks (1 - p) p p (1 - p)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        E₁ * (Matrix.fromBlocks
            (Matrix.diagonal fun i => if ∃ j, π i j = 1 then (0 : K) else 1) π πᵀ
            (Matrix.diagonal fun j => if ∃ i, π i j = 1 then (0 : K) else 1)).submatrix
              finSumFinEquiv.symm finSumFinEquiv.symm * E₂ := by
  obtain ⟨E₁, Pm, E₂, h1, h2, h3, h4, h01', hrow', hcol', -, hS⟩ := bruhat_exists (Smat p)
  have hpr := p_rank p F₁ π F₂ hF₁ hd₁ hF₂ hd₂ h01 hrow hcol hfac
  have hW01 : ∀ a b, Wmat π a b = 0 ∨ Wmat π a b = 1 := by
    intro a b
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rcases a with i | i <;> rcases b with j | j <;>
      simp only [Wmat, submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, diagonal_apply,
        transpose_apply]
    · split_ifs <;> simp
    · exact h01 i j
    · exact h01 j i
    · split_ifs <;> simp
  have hPm : Pm = Wmat π := by
    refine pp_uniq Pm (Wmat π) h01' hW01 fun X Y => ?_
    rw [← bruhat_rank_nat E₁ Pm E₂ h1 h2 h3 h4 h01' hrow' hcol', ← hS]
    exact corner p π hp hrow hcol hpr X Y
  refine ⟨E₁, E₂, h1, h2, h3, h4, ?_⟩
  rw [hPm] at hS
  exact hS

