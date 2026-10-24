-- Prove2me | solution 1 for MatrixAnalytic.Taboo.limiting_vector_taboo
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:27:13.428576+00:00
-- url     : https://prove2.me/submissions/81624e45-df67-4caf-bcc0-805097ab92b8

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices

-- ==== Base ====

open scoped ENNReal
open MatrixAnalytic.Taboo

noncomputable def x5tb_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def x5tb_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then x5tb_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma x5tb_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5tb_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * x5tb_W P ω := by
  unfold x5tb_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma x5tb_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    x5tb_W P (Fin.snoc ω k : Fin (n + 2) → V) = x5tb_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold x5tb_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma x5tb_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma x5tb_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma x5tb_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma x5tb_PS_zero (x y : V) (A : V → Prop) :
    x5tb_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold x5tb_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [x5tb_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma x5tb_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.cons x ω : Fin (L + 2) → V) 0 = x ∧ (Fin.cons x ω : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.cons x ω : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω 0)) ∧ ω 0 = ω 0 ∧ ω (Fin.last L) = y ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)) := by
  rw [← Fin.succ_last, Fin.cons_succ, Fin.cons_zero, Fin.forall_fin_succ]
  simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff, true_and, Fin.cons_succ,
    Fin.succ_ne_zero, not_false_eq_true, true_implies, Fin.succ_inj]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m _ hm => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 0 ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hm0 : m = 0
    · subst hm0
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm0 hm

lemma x5tb_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5tb_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then x5tb_PS P z L y A else 0) := by
  classical
  unfold x5tb_PS
  rw [x5tb_tsum_cons, tsum_eq_single x]
  · simp_rw [x5tb_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := x5tb_cond_cons x y A ω
      rw [x5tb_W_cons]
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd (hcc.mp h1).2 h3
      · exact absurd (hcc.mp h1).1 h2
      · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
      · simp
      · simp
    · intro z hz
      simp [Ne.symm hz]
  · intro k hk
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma x5tb_PS_one (x y : V) (A : V → Prop) :
    x5tb_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [x5tb_PS_cons P, tsum_eq_single y]
  · simp [x5tb_PS_zero]
  · intro z hz; simp [x5tb_PS_zero, hz]

open Classical in
noncomputable def x5tb_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then x5tb_W P ω else 0

open Classical in
noncomputable def x5tb_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then x5tb_W P ω else 0

lemma x5tb_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5tb_AV P x A (t + 1) + x5tb_EX P x A (t + 1) = x5tb_AV P x A t := by
  classical
  unfold x5tb_AV x5tb_EX
  rw [x5tb_tsum_snoc, x5tb_tsum_snoc, ← ENNReal.tsum_add]
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_add]
  have hz : ∀ k, (Fin.snoc ω k : Fin (t + 2) → V) 0 = ω 0 := fun k => by
    have : (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  have e1 : ∀ m : Fin (t + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have hA : ∀ k, (∀ i : Fin (t + 2), i ≠ 0 → A ((Fin.snoc ω k : Fin (t + 2) → V) i)) ↔
      (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have e2 : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp only [ne_eq, e1, e2, not_false_eq_true, true_implies]
  have hB : ∀ k, (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
      A ((Fin.snoc ω k : Fin (t + 2) → V) m)) ↔ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff,
      and_true]
    refine forall_congr' fun m => ?_
    have e2 : m.castSucc ≠ Fin.last (t+1) := Fin.castSucc_ne_last m
    simp only [e1, e2, not_false_eq_true, true_implies]
  simp_rw [hz, hA, hB, Fin.snoc_last, x5tb_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        x5tb_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        x5tb_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        x5tb_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
      intro k
      by_cases hk : A k
      · rw [if_pos ⟨hc.1, hc.2, hk⟩, if_neg (by tauto), add_zero]
      · rw [if_neg (by tauto), if_pos ⟨hc.1, hk, hc.2⟩, zero_add]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, hrow, mul_one]
  · rw [if_neg hc]
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [if_neg (by tauto), if_neg (by tauto), add_zero]

lemma x5tb_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5tb_AV P x A t + ∑ k ∈ Finset.range t, x5tb_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold x5tb_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [x5tb_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (x5tb_EX P x A (t + 1)), ← add_assoc,
      add_comm (x5tb_EX P x A (t + 1)), x5tb_step P hrow x A t, ih]

lemma x5tb_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    x5tb_PS P x k y A ≤ x5tb_EX P x A k := by
  classical
  unfold x5tb_PS x5tb_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma x5tb_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, x5tb_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← x5tb_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => x5tb_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma x5tb_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → x5tb_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5tb_PS P x (s + 1) z (fun z => m + 1 < lev z) * x5tb_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [x5tb_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', x5tb_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then x5tb_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        x5tb_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * x5tb_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [x5tb_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        x5tb_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        x5tb_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          x5tb_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5tb_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          x5tb_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          x5tb_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          x5tb_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          x5tb_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [x5tb_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
        by_cases hz : lev z = m + 1
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun w => ?_
          by_cases hw : m + 1 < lev w
          · simp [hw, mul_assoc]
          · simp [hw]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hw : m + 1 < lev w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hw1 : lev w = m + 1
    · simp [hw1]
    · by_cases hw2 : m + 1 < lev w
      · rw [if_pos (Or.inr (by omega)), ih w (by omega)]
        simp [hw1, hw2]
      · have hw3 : ¬ m < lev w := by omega
        simp [hw1, hw2, hw3]
end Gen

section Gen3
variable {V : Type*} (P : V → V → ℝ)

lemma x5tb_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
    ((Fin.snoc ω y : Fin (L + 2) → V) 0 = x ∧ (Fin.snoc ω y : Fin (L + 2) → V) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.snoc ω y : Fin (L + 2) → V) m)) ↔
    ((L = 0 ∨ A (ω (Fin.last L))) ∧ (ω 0 = x ∧ ω (Fin.last L) = ω (Fin.last L) ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m))) := by
  have hz : (Fin.snoc ω y : Fin (L + 2) → V) 0 = ω 0 := by
    have : (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  rw [hz, Fin.snoc_last, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff, and_true,
    true_and]
  have e1 : ∀ m : Fin (L + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · rintro rfl; rfl
  have e2 : ∀ m : Fin (L + 1), m.castSucc ≠ Fin.last (L+1) := Fin.castSucc_ne_last
  simp only [e1, e2, not_false_eq_true, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, fun m hm _ => h2 m hm⟩
    by_cases hL : L = 0
    · exact Or.inl hL
    · refine Or.inr (h2 _ ?_)
      intro h; apply hL; have := congrArg Fin.val h; simp at this; omega
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun m hm => ?_⟩
    by_cases hml : m = Fin.last L
    · subst hml
      rcases h0 with h0 | h0
      · subst h0; exact absurd rfl hm
      · exact h0
    · exact h2 m hm hml

lemma x5tb_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    x5tb_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then x5tb_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold x5tb_PS
  rw [x5tb_tsum_snoc]
  simp_rw [x5tb_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := x5tb_cond_snoc x y A ω
    rw [x5tb_W_snoc]
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (hcc.mp h1).2 h3
    · exact absurd (hcc.mp h1).1 h2
    · exact absurd (hcc.mpr ⟨by assumption, by assumption⟩) (by assumption)
    · simp
    · simp
  · intro z hz
    simp [Ne.symm hz]
  · intro k hk
    rw [if_neg]
    rintro ⟨-, h, -⟩
    exact hk (by simpa using h)

/-- last-visit decomposition -/
lemma x5tb_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → x5tb_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5tb_PS P x s z A * x5tb_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [x5tb_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, x5tb_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, x5tb_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [x5tb_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, x5tb_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then x5tb_PS P x (L + 1) z A *
        x5tb_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then x5tb_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, x5tb_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        x5tb_PS P x s z A * x5tb_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          x5tb_PS P x s z A * x5tb_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          x5tb_PS P x s z A * x5tb_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          x5tb_PS P x s z A * x5tb_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, x5tb_PS_snoc P z (L + 1 - s)]
        by_cases hz : mid z
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun w => ?_
          have : ¬ (L + 1 - s = 0) := by omega
          by_cases hw : A' w
          · simp [hw, this, mul_assoc]
          · simp [hw, this]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_right]
      by_cases hw : A' w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.sum_mul]
    by_cases hPw : P w y = 0
    · simp [hPw]
    rcases hstep w y hy hPw with ⟨hm, hA, hA'⟩ | ⟨hA', hA, hI, hm⟩ | ⟨hA, hA', hm⟩
    · simp [hm, hA, hA']
    · rw [if_pos (Or.inr hA), ih w hI]
      simp [hm, hA']
    · simp [hA, hA', hm]

lemma x5tb_cauchy0 (a b : ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) = (∑' s, a s) * ∑' u, b u := by
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun s t => a s * b t),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal k)
    (fun p : ℕ × ℕ => a p.1 * b p.2), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun s t => a s * b t)]

end Gen3
lemma x5tb_swap0 {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact x5tb_cauchy0 (a z) (b z)
  · simp [hz]

section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5tb_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5tb_EX P x A k = ∑' y, if ¬ A y then x5tb_PS P x k y A else 0 := by
  classical
  unfold x5tb_EX x5tb_PS
  simp_rw [x5tb_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma x5tb_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    x5tb_AV P x A (k + 1) = ∑' y, if A y then x5tb_PS P x (k + 1) y A else 0 := by
  classical
  unfold x5tb_AV x5tb_PS
  simp_rw [x5tb_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last (k + 1)))]
  · by_cases hA : A (ω (Fin.last (k + 1)))
    · simp only [hA, if_true, true_and]
      congr 1
      apply propext
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun m hm _ => h2 m hm⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun m hm => ?_⟩
        by_cases hl : m = Fin.last (k + 1)
        · rw [hl]; exact hA
        · exact h2 m hm hl
    · simp only [hA, if_false]
      rw [if_neg]
      rintro ⟨-, h2⟩
      exact hA (h2 _ (by simp [Fin.ext_iff]))
  · intro y hy; simp [Ne.symm hy]

lemma x5tb_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    x5tb_PS P x L y A ≤ x5tb_PS P x L y A' := by
  classical
  unfold x5tb_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma x5tb_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, x5tb_PS P x u y A * x5tb_PS P y t z A ≤ x5tb_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [x5tb_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [x5tb_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      x5tb_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), x5tb_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma x5tb_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : x5tb_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, x5tb_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [x5tb_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [x5tb_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then x5tb_PS P x0 s z (fun _ => True) *
      x5tb_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma x5tb_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK


section BDGen
variable {V : Type*} (P : V → V → ℝ)

lemma x5tb_AV_zero (x : V) (A : V → Prop) : x5tb_AV P x A 0 = 1 := by
  classical
  unfold x5tb_AV
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  rw [tsum_eq_single x]
  · simp [x5tb_W]
  · intro b hb; simp [hb]

lemma x5tb_AV_anti (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5tb_AV P x A (t + 1) ≤ x5tb_AV P x A t := by
  rw [← x5tb_step P hrow x A t]; exact le_self_add

lemma x5tb_PS_le_AV (x y : V) (A : V → Prop) (hy : A y) (t : ℕ) :
    x5tb_PS P x t y A ≤ x5tb_AV P x A t := by
  classical
  unfold x5tb_PS x5tb_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → A (ω m)
  · rw [if_pos h, if_pos]
    refine ⟨h.1, fun i hi => ?_⟩
    by_cases hl : i = Fin.last t
    · rw [hl, h.2.1]; exact hy
    · exact h.2.2 i hi hl
  · rw [if_neg h]; exact bot_le

lemma x5tb_AV_concat (A : V → Prop) (x z : V) (hz : A z) (u t : ℕ) :
    x5tb_PS P x u z A * x5tb_AV P z A t ≤ x5tb_AV P x A (u + t) := by
  classical
  rcases t with _ | s
  · rw [x5tb_AV_zero, mul_one, add_zero]; exact x5tb_PS_le_AV P x z A hz u
  · rw [x5tb_AV_eq P z A s, show u + (s + 1) = (u + s) + 1 by omega, x5tb_AV_eq P x A (u + s),
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun y => ?_
    split_ifs with hy
    · have := x5tb_PS_concat P A z y hz u x (s + 1)
      rwa [show u + (s + 1) = u + s + 1 by omega] at this
    · simp

lemma x5tb_stepPow_nonneg [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y; simp only [stepPow]
    exact tsum_nonneg fun z => mul_nonneg (ih x z) (hP0 z y)

lemma x5tb_stepPow_PS [Countable V] [DecidableEq V] (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ t x y, 0 < stepPow P t x y → x5tb_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [stepPow] at h
    rw [x5tb_PS_zero]
    split_ifs at h with hyx
    · rw [if_pos hyx.symm]; exact one_ne_zero
    · exact absurd h (lt_irrefl 0)
  | succ t ih =>
    intro x y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, 0 < stepPow P t x z * P z y := by
      by_contra hc
      push_neg at hc
      have : ∀ z, stepPow P t x z * P z y = 0 := fun z =>
        le_antisymm (hc z) (mul_nonneg (x5tb_stepPow_nonneg P hP0 t x z) (hP0 z y))
      simp [this] at h
    have ha := x5tb_stepPow_nonneg P hP0 t x z
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne ha (fun h0 => by rw [← h0, zero_mul] at hz; exact lt_irrefl 0 hz)
    have h2 : 0 < P z y :=
      lt_of_le_of_ne (hP0 z y) (fun h0 => by rw [← h0, mul_zero] at hz; exact lt_irrefl 0 hz)
    rw [x5tb_PS_snoc P x t y (fun _ => True)]
    intro h0
    have := (ENNReal.tsum_eq_zero.mp h0) z
    rw [if_pos (Or.inr trivial)] at this
    rcases mul_eq_zero.mp this with h3 | h3
    · exact ih x z h1 h3
    · exact absurd h3 (by simpa using h2)

lemma x5tb_AV_le_one (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    x5tb_AV P x A t ≤ 1 :=
  le_self_add.trans_eq (x5tb_mass P hrow x A t)

end BDGen

-- ==== Gen ====

open scoped ENNReal
open MatrixAnalytic.Taboo
open Filter Topology

section NHTab
variable {V : Type*} (P : V → V → ℝ)

lemma x5tb_recur (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x0 : V)
    (hret : Tendsto (fun t => x5tb_AV P x0 (fun z => z ≠ x0) t) atTop (𝓝 0))
    (hreach : ∀ z, z ≠ x0 → ∃ u, x5tb_PS P x0 u z (fun z => z ≠ x0) ≠ 0) :
    ∀ z, Tendsto (fun t => x5tb_AV P z (fun w => w ≠ x0) t) atTop (𝓝 0) := by
  intro z
  by_cases hz : z = x0
  · subst hz; exact hret
  obtain ⟨u, hu⟩ := hreach z hz
  set c := x5tb_PS P x0 u z (fun z => z ≠ x0) with hc
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((x5tb_PS_le_AV P x0 z _ hz u).trans (x5tb_AV_le_one P hrow x0 _ u))
  have hb : ∀ t, x5tb_AV P z (fun w => w ≠ x0) t ≤ c⁻¹ * x5tb_AV P x0 (fun w => w ≠ x0) (t + u) := by
    intro t
    have h1 := x5tb_AV_concat P (fun w => w ≠ x0) x0 z hz u t
    rw [add_comm u t] at h1
    calc x5tb_AV P z (fun w => w ≠ x0) t = c⁻¹ * (c * x5tb_AV P z (fun w => w ≠ x0) t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hu hctop, one_mul]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun t => c⁻¹ * x5tb_AV P x0 (fun w => w ≠ x0) (t + u)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((Filter.tendsto_add_atTop_iff_nat u).mpr hret)
      (Or.inr (ENNReal.inv_ne_top.mpr hu))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => bot_le) hb

/-- The taboo identity: an invariant measure of finite mass is determined on `A` by its values
off `A`, provided the chain leaves `A` almost surely from every state of `A`. -/
theorem x5tb_taboo (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (ν : V → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (A : V → Prop) [DecidablePred A]
    (hAV : ∀ z, A z → Tendsto (fun t => x5tb_AV P z A t) atTop (𝓝 0)) :
    ∀ y, A y → ν y = ∑' x, if A x then 0 else ν x * ∑' t, x5tb_PS P x (t + 1) y A := by
  classical
  intro y hy
  set a : ℕ → ℝ≥0∞ := fun t => ∑' x, if A x then 0 else ν x * x5tb_PS P x (t + 1) y A with ha
  set r : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then ν z * x5tb_PS P z t y A else 0 with hr
  have hcons : ∀ t x, x5tb_PS P x (t + 1) y A =
      ∑' z, if A z then ENNReal.ofReal (P x z) * x5tb_PS P z t y A else 0 := by
    intro t x
    rw [x5tb_PS_cons P x t y A]
    refine tsum_congr fun z => ?_
    by_cases hAz : A z
    · rw [if_pos (Or.inr hAz), if_pos hAz]
    · rw [if_neg hAz]
      by_cases ht : t = 0
      · subst ht
        rw [if_pos (Or.inl rfl), x5tb_PS_zero, if_neg (fun (h : z = y) => hAz (h ▸ hy)), mul_zero]
      · rw [if_neg (by tauto), mul_zero]
  have hstep : ∀ t, r t = a t + r (t + 1) := by
    intro t
    have e1 : r t = ∑' x, ν x * x5tb_PS P x (t + 1) y A := by
      simp only [hr, hcons]
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun z => ?_
      by_cases hAz : A z
      · simp only [if_pos hAz]
        rw [← hinv z, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun x => ?_
        ring
      · simp [hAz]
    rw [e1, ha, hr, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    by_cases hAx : A x <;> simp [hAx]
  have hr0 : r 0 = ν y := by
    simp only [hr]
    rw [tsum_eq_single y]
    · rw [if_pos hy, x5tb_PS_zero, if_pos rfl, mul_one]
    · intro z hz; rw [x5tb_PS_zero, if_neg hz]; simp
  have hsum : ∀ t, ν y = ∑ s ∈ Finset.range t, a s + r t := by
    intro t
    induction t with
    | zero => simp [hr0]
    | succ t ih => rw [ih, hstep t, Finset.sum_range_succ, add_assoc]
  -- the remainder tends to zero (dominated convergence for the counting measure)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    letI : MeasurableSpace V := ⊤
    have hdc := MeasureTheory.tendsto_lintegral_of_dominated_convergence (μ := MeasureTheory.Measure.count)
      (F := fun t z => if A z then ν z * x5tb_AV P z A t else 0) (f := fun _ => 0) ν
      (fun t => measurable_from_top)
      (fun t => Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          calc ν z * x5tb_AV P z A t ≤ ν z * 1 := by gcongr; exact x5tb_AV_le_one P hrow z A t
            _ = ν z := mul_one _
        · simp [hAz])
      (by rw [MeasureTheory.lintegral_count' measurable_from_top]; exact hfin)
      (Filter.Eventually.of_forall fun z => by
        by_cases hAz : A z
        · simp only [if_pos hAz]
          have hνz : ν z ≠ ⊤ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum z)
          simpa using ENNReal.Tendsto.const_mul (hAV z hAz) (Or.inr hνz)
        · simp [hAz])
    rw [MeasureTheory.lintegral_zero] at hdc
    simp_rw [MeasureTheory.lintegral_count' measurable_from_top] at hdc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdc (fun t => bot_le) ?_
    intro t
    simp only [hr]
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hAz : A z
    · simp only [if_pos hAz]; gcongr; exact x5tb_PS_le_AV P z y A hy t
    · simp [hAz]
  have hlim : Tendsto (fun t => ∑ s ∈ Finset.range t, a s + r t) atTop (𝓝 (∑' s, a s + 0)) :=
    (ENNReal.tendsto_nat_tsum a).add hrlim
  have hconst : Tendsto (fun t => ∑ s ∈ Finset.range t, a s + r t) atTop (𝓝 (ν y)) := by
    simp_rw [← hsum]; exact tendsto_const_nhds
  rw [tendsto_nhds_unique hconst hlim, add_zero, ha]
  dsimp only
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  by_cases hAx : A x
  · simp [hAx]
  · simp only [if_neg hAx]; rw [ENNReal.tsum_mul_left]


lemma x5tb_AV_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x : V) (t : ℕ) :
    x5tb_AV P x A t ≤ x5tb_AV P x A' t := by
  classical
  unfold x5tb_AV
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos h, if_pos ⟨h.1, fun i hi => hAA _ (h.2 i hi)⟩]
  · rw [if_neg h]; exact bot_le


end NHTab

section NHLim
variable {V : Type*} (P : V → V → ℝ)

lemma x5tb_hasSum_of_ennreal {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (h : ∑' a, ENNReal.ofReal (f a) = 1) : HasSum f 1 := by
  have hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤ := by rw [h]; exact ENNReal.one_ne_top
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  have h2 := x5tb_ofReal_tsum f hf hne
  rw [h] at h2
  have h3 : ∑' a, f a = 1 := by
    have := congrArg ENNReal.toReal h2
    simpa [ENNReal.toReal_ofReal (tsum_nonneg hf)] using this
  exact h3 ▸ hs.hasSum

lemma x5tb_P_le_one (hP : IsStochasticC P) (x y : V) : P x y ≤ 1 :=
  le_hasSum (hP.2 x) y (fun z _ => hP.1 x z)

lemma x5tb_summ_mul [Countable V] [DecidableEq V] (hP : IsStochasticC P) (s : V → ℝ)
    (hs0 : ∀ z, 0 ≤ s z) (hs : Summable s) (y : V) : Summable fun z => s z * P z y :=
  Summable.of_nonneg_of_le (fun z => mul_nonneg (hs0 z) (hP.1 z y))
    (fun z => mul_le_of_le_one_right (hs0 z) (x5tb_P_le_one P hP z y)) hs

lemma x5tb_stepPow_hasSum [Countable V] [DecidableEq V] (hP : IsStochasticC P) :
    ∀ t x, HasSum (fun y => stepPow P t x y) 1 := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  intro t
  induction t with
  | zero =>
    intro x
    simp only [stepPow]
    exact hasSum_ite_eq x 1
  | succ t ih =>
    intro x
    have hs0 := x5tb_stepPow_nonneg P hP0 t x
    refine x5tb_hasSum_of_ennreal _ (x5tb_stepPow_nonneg P hP0 (t + 1) x) ?_
    simp only [stepPow]
    have e : ∀ y, ENNReal.ofReal (∑' z, stepPow P t x z * P z y) =
        ∑' z, ENNReal.ofReal (stepPow P t x z) * ENNReal.ofReal (P z y) := by
      intro y
      rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (hs0 z) (hP0 z y))
        (x5tb_summ_mul P hP _ hs0 (ih x).summable y)]
      exact tsum_congr fun z => ENNReal.ofReal_mul (hs0 z)
    simp_rw [e]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hs0 (ih x).summable, (ih x).tsum_eq, ENNReal.ofReal_one]

lemma x5tb_limit_stat [Countable V] [DecidableEq V] [Nonempty V] (hP : IsStochasticC P)
    (π : V → ℝ) (hlim : ∀ x y, Tendsto (fun t => stepPow P t x y) atTop (𝓝 (π y))) :
    (∀ y, 0 ≤ π y) ∧ (∑' y, ENNReal.ofReal (π y) ≤ 1) ∧
      ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) = ENNReal.ofReal (π y) := by
  classical
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  set x0 : V := Classical.arbitrary V
  have hnn : ∀ y, 0 ≤ π y := fun y =>
    ge_of_tendsto (hlim x0 y) (Eventually.of_forall fun t => x5tb_stepPow_nonneg P hP0 t x0 y)
  have hmass : ∑' y, ENNReal.ofReal (π y) ≤ 1 := by
    refine ENNReal.summable.tsum_le_of_sum_le fun F => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hnn y), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_of_tendsto' (tendsto_finset_sum F fun y _ => hlim x0 y) fun t => ?_
    exact sum_le_hasSum F (fun y _ => x5tb_stepPow_nonneg P hP0 t x0 y)
      (x5tb_stepPow_hasSum P hP t x0)
  have hsup : ∀ y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) ≤ ENNReal.ofReal (π y) := by
    intro y
    refine ENNReal.summable.tsum_le_of_sum_le fun F => ?_
    have e : ∑ x ∈ F, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) =
        ENNReal.ofReal (∑ x ∈ F, π x * P x y) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (hnn x) (hP0 x y))]
      exact Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_mul (hnn x)).symm
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Tendsto (fun t => ∑ x ∈ F, stepPow P t x0 x * P x y) atTop
        (𝓝 (∑ x ∈ F, π x * P x y)) :=
      tendsto_finset_sum F fun x _ => (hlim x0 x).mul_const _
    have h2 : Tendsto (fun t => stepPow P (t + 1) x0 y) atTop (𝓝 (π y)) :=
      (hlim x0 y).comp (tendsto_add_atTop_nat 1)
    refine le_of_tendsto_of_tendsto' h1 h2 fun t => ?_
    have hs0 := x5tb_stepPow_nonneg P hP0 t x0
    show _ ≤ ∑' z, stepPow P t x0 z * P z y
    exact (x5tb_summ_mul P hP _ hs0 (x5tb_stepPow_hasSum P hP t x0).summable y).sum_le_tsum F
      (fun z _ => mul_nonneg (hs0 z) (hP0 z y))
  refine ⟨hnn, hmass, fun y => ?_⟩
  by_contra hne
  have hlt := lt_of_le_of_ne (hsup y) hne
  have hfin : ∑' y, ∑' x, ENNReal.ofReal (π x) * ENNReal.ofReal (P x y) ≠ ⊤ := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hrow, mul_one]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hmass
  have := ENNReal.tsum_lt_tsum hfin hsup hlt
  rw [ENNReal.tsum_comm] at this
  simp_rw [ENNReal.tsum_mul_left, hrow, mul_one] at this
  exact lt_irrefl _ this

end NHLim

-- ==== Exit ====

open scoped ENNReal
open MatrixAnalytic.Taboo
open Filter Topology

section TBExit
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma x5tb_AV_cons (z : V) (A : V → Prop) (t : ℕ) :
    x5tb_AV P z A (t + 1) =
      ∑' w, ENNReal.ofReal (P z w) * (if A w then x5tb_AV P w A t else 0) := by
  classical
  rw [x5tb_AV_eq]
  simp_rw [x5tb_PS_cons P z t]
  simp_rw [x5tb_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun w => ?_
  have e : ∀ y, (if A y then ENNReal.ofReal (P z w) *
      (if t = 0 ∨ A w then x5tb_PS P w t y A else 0) else 0) =
      ENNReal.ofReal (P z w) * (if A y then (if t = 0 ∨ A w then x5tb_PS P w t y A else 0)
        else 0) := by
    intro y; split_ifs <;> simp
  simp_rw [e, ENNReal.tsum_mul_left]
  congr 1
  rcases t with _ | s
  · simp only [true_or, if_true, x5tb_PS_zero, x5tb_AV_zero]
    rw [tsum_eq_single w]
    · by_cases hw : A w <;> simp [hw]
    · intro y hy; simp [Ne.symm hy]
  · by_cases hw : A w
    · simp only [hw, or_true, if_true]
      rw [x5tb_AV_eq]
    · simp [hw]

lemma x5tb_nu_ge (ν : V → ℝ≥0∞) (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (x : V) :
    ∀ t z, ν x * x5tb_PS P x t z (fun _ => True) ≤ ν z := by
  classical
  intro t
  induction t with
  | zero =>
    intro z
    rw [x5tb_PS_zero]
    split_ifs with h
    · subst h; simp
    · simp
  | succ t ih =>
    intro z
    rw [x5tb_PS_snoc]
    simp only [or_true, if_true]
    rw [← hinv z, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [← mul_assoc]
    gcongr
    exact ih w

lemma x5tb_cut (T : V → Prop) [DecidablePred T] (x0 y : V) (hx0 : T x0) (hy : ¬ T y) (L : ℕ)
    (h : x5tb_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ z u, T z ∧ x5tb_PS P z u y (fun w => ¬ T w) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [x5tb_PS_zero, if_neg (by rintro rfl; exact hy hx0)] at h; exact absurd rfl h
  rw [x5tb_conv3 P (fun _ => True) T (fun _ => True) (fun w => ¬ T w) x0 hx0
    (fun w _ _ _ => by by_cases hw : T w <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if T z then x5tb_PS P x0 s z (fun _ => True) *
      x5tb_PS P z (L + 1 - s) y (fun w => ¬ T w) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzT : T z
  · rw [if_pos hzT] at hz
    exact ⟨z, _, hzT, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzT] at hz; exact absurd rfl hz

/-- Under an invariant measure of finite mass that charges every state of `T`, the chain started
in `T` returns to `T` almost surely. -/
theorem x5tb_exit_as (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (ν : V → ℝ≥0∞)
    (hinv : ∀ y, ∑' x, ν x * ENNReal.ofReal (P x y) = ν y) (hfin : ∑' x, ν x ≠ ⊤)
    (T : V → Prop) [DecidablePred T] (hpos : ∀ z, T z → ν z ≠ 0) :
    ∀ z, T z → Tendsto (fun t => x5tb_AV P z (fun w => ¬ T w) t) atTop (𝓝 0) := by
  classical
  set A : V → Prop := fun w => ¬ T w with hA
  set a : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then ν z * x5tb_AV P z A t else 0 with ha
  set b : ℕ → ℝ≥0∞ := fun t => ∑' z, if A z then 0 else ν z * x5tb_AV P z A (t + 1) with hb
  have hab : ∀ t, a (t + 1) + b t = a t := by
    intro t
    rw [ha, hb]
    dsimp only
    rw [← ENNReal.tsum_add]
    have e1 : ∀ z, ((if A z then ν z * x5tb_AV P z A (t + 1) else 0) +
        if A z then 0 else ν z * x5tb_AV P z A (t + 1)) = ν z * x5tb_AV P z A (t + 1) := by
      intro z; split_ifs <;> simp
    simp_rw [e1, x5tb_AV_cons P _ A t, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun w => ?_
    simp_rw [← mul_assoc]
    rw [ENNReal.tsum_mul_right, hinv w]
    split_ifs <;> simp
  have ha0 : a 0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun z => ?_)
    split_ifs
    · rw [x5tb_AV_zero, mul_one]
    · exact bot_le
  have hsum : ∀ N, a 0 = a N + ∑ t ∈ Finset.range N, b t := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [ih, Finset.sum_range_succ, ← hab N]; ring
  set h : V → ℝ≥0∞ := fun z => ⨅ t, x5tb_AV P z A t with hh
  set binf := ∑' z, if A z then 0 else ν z * h z with hbinf
  have hbt : ∀ t, binf ≤ b t := by
    intro t
    refine ENNReal.tsum_le_tsum fun z => ?_
    split_ifs
    · exact le_rfl
    · gcongr; exact iInf_le _ _
  have hb0 : binf = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hne ha0
    have : (N : ℝ≥0∞) * binf ≤ a 0 := by
      rw [hsum N]
      refine le_trans ?_ le_add_self
      calc (N : ℝ≥0∞) * binf = ∑ t ∈ Finset.range N, binf := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun t _ => hbt t
    exact lt_irrefl _ (hN.trans_le this)
  intro z hz
  have hz0 : ν z * h z = 0 := by
    have := (ENNReal.tsum_eq_zero.mp hb0) z
    rwa [if_neg (by simp [hA, hz])] at this
  have hhz : h z = 0 := (mul_eq_zero.mp hz0).resolve_left (hpos z hz)
  have hanti : Antitone fun t => x5tb_AV P z A t :=
    antitone_nat_of_succ_le fun t => x5tb_AV_anti P hrow z A t
  have := tendsto_atTop_iInf hanti
  rwa [show (⨅ t, x5tb_AV P z A t) = 0 from hhz] at this

/-- propagation from a state of `T` to a state reachable from it while avoiding `T` -/
lemma x5tb_prop (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (A : V → Prop) (z u : V)
    (hu : A u) (s : ℕ) (hc : x5tb_PS P z s u A ≠ 0)
    (hz : Tendsto (fun t => x5tb_AV P z A t) atTop (𝓝 0)) :
    Tendsto (fun t => x5tb_AV P u A t) atTop (𝓝 0) := by
  set c := x5tb_PS P z s u A with hcd
  have hctop : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((x5tb_PS_le_AV P z u _ hu s).trans (x5tb_AV_le_one P hrow z _ s))
  have hb : ∀ t, x5tb_AV P u A t ≤ c⁻¹ * x5tb_AV P z A (t + s) := by
    intro t
    have h1 := x5tb_AV_concat P A z u hu s t
    rw [add_comm s t] at h1
    calc x5tb_AV P u A t = c⁻¹ * (c * x5tb_AV P u A t) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc hctop, one_mul]
      _ ≤ _ := by gcongr
  have hlim : Tendsto (fun t => c⁻¹ * x5tb_AV P z A (t + s)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((Filter.tendsto_add_atTop_iff_nat s).mpr hz)
      (Or.inr (ENNReal.inv_ne_top.mpr hc))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => bot_le) hb

end TBExit

theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (π : S → ℝ)
    (hlim : ∀ i j : S, Filter.Tendsto (fun k => stepPow P k i j) Filter.atTop (nhds (π j)))
    (T D : Set S) (hT : T.Nonempty) (hTD : Disjoint T D) :
    ∀ j ∈ D, ENNReal.ofReal (π j) = ∑' i : T, ENNReal.ofReal (π i) * tabooR P T i j := by
  classical
  intro j hj
  have hjT : j ∉ T := fun h => Set.disjoint_left.mp hTD h hj
  obtain ⟨x0, hx0⟩ := hT
  haveI : Nonempty S := ⟨x0⟩
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  obtain ⟨hnn, hmass, hinv⟩ := x5tb_limit_stat P hP π hlim
  set ν : S → ℝ≥0∞ := fun x => ENNReal.ofReal (π x) with hν
  by_cases h0 : ∀ y, π y = 0
  · simp [h0]
  push Not at h0
  obtain ⟨y0, hy0⟩ := h0
  have hν0 : ν y0 ≠ 0 := by
    simp only [hν, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact lt_of_le_of_ne (hnn y0) (Ne.symm hy0)
  have hpos : ∀ z, ν z ≠ 0 := by
    intro z
    obtain ⟨t, ht⟩ := hirr y0 z
    have h1 := x5tb_nu_ge P ν hinv y0 t z
    intro hz
    rw [hz] at h1
    exact mul_ne_zero hν0 (x5tb_stepPow_PS P hP0 t y0 z ht) (le_antisymm h1 bot_le)
  have hfin : ∑' x, ν x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hmass
  have hT' := x5tb_exit_as P hrow ν hinv hfin (fun w => w ∈ T) (fun z _ => hpos z)
  have hAV : ∀ u, (fun w => w ∉ T) u →
      Tendsto (fun t => x5tb_AV P u (fun w => w ∉ T) t) atTop (𝓝 0) := by
    intro u hu
    obtain ⟨t, ht⟩ := hirr x0 u
    obtain ⟨z, s, hz, hs⟩ := x5tb_cut P (fun w => w ∈ T) x0 u hx0 hu t
      (x5tb_stepPow_PS P hP0 t x0 u ht)
    exact x5tb_prop P hrow _ z u hu s hs (hT' z hz)
  have htab := x5tb_taboo P hrow ν hinv hfin (fun w => w ∉ T) hAV j hjT
  show ν j = _
  rw [htab, tsum_subtype T (fun x => ENNReal.ofReal (π x) * tabooR P T x j)]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ T
  · rw [if_neg (by simp [hx]), Set.indicator_of_mem hx]
    congr 1
    unfold tabooR
    have e0 : tabooP P T 0 x j = 0 := by
      unfold tabooP
      refine ENNReal.tsum_eq_zero.mpr fun ω => ?_
      rw [if_neg]
      rintro ⟨h1, h2, -⟩
      exact hjT (by rw [← h2, show Fin.last 0 = 0 from rfl, h1]; exact hx)
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable, e0, zero_add]
    refine tsum_congr fun t => ?_
    unfold tabooP x5tb_PS pathWeightE x5tb_W ennP
    refine tsum_congr fun ω => ?_
    split_ifs <;> rfl
  · rw [if_pos hx, Set.indicator_of_notMem hx]

