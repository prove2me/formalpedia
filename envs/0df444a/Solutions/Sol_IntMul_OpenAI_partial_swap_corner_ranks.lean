-- Prove2me | solution 1 for IntMul.OpenAI.partial_swap_corner_ranks
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T14:21:39.061052+00:00
-- url     : https://prove2.me/submissions/d5ef9411-4e97-4f95-adf5-c710b26ec434

import Mathlib

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

theorem solution {m : ℕ} {K : Type*} [Field K] (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
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
