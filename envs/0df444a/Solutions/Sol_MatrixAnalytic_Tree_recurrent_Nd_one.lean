-- Prove2me | solution 1 for MatrixAnalytic.Tree.recurrent_Nd_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:17:02.107824+00:00
-- url     : https://prove2.me/submissions/790942ad-6971-4c01-b7ef-55dac7077384

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_MatrixAnalytic_Tree_Model

open scoped ENNReal
open MatrixAnalytic.Tree

noncomputable def g72mab_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def g72mab_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then g72mab_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * g72mab_W P ω := by
  unfold g72mab_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma g72mab_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72mab_W P (Fin.snoc ω k : Fin (n + 2) → V) = g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold g72mab_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g72mab_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g72mab_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g72mab_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma g72mab_PS_zero (x y : V) (A : V → Prop) :
    g72mab_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g72mab_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g72mab_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma g72mab_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g72mab_PS P z L y A else 0) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_cons, tsum_eq_single x]
  · simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g72mab_cond_cons x y A ω
      rw [g72mab_W_cons]
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

lemma g72mab_PS_one (x y : V) (A : V → Prop) :
    g72mab_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g72mab_PS_cons P, tsum_eq_single y]
  · simp [g72mab_PS_zero]
  · intro z hz; simp [g72mab_PS_zero, hz]

open Classical in
noncomputable def g72mab_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then g72mab_W P ω else 0

open Classical in
noncomputable def g72mab_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then g72mab_W P ω else 0

lemma g72mab_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A (t + 1) + g72mab_EX P x A (t + 1) = g72mab_AV P x A t := by
  classical
  unfold g72mab_AV g72mab_EX
  rw [g72mab_tsum_snoc, g72mab_tsum_snoc, ← ENNReal.tsum_add]
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
  simp_rw [hz, hA, hB, Fin.snoc_last, g72mab_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        g72mab_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
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

lemma g72mab_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72mab_AV P x A t + ∑ k ∈ Finset.range t, g72mab_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g72mab_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [g72mab_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g72mab_EX P x A (t + 1)), ← add_assoc,
      add_comm (g72mab_EX P x A (t + 1)), g72mab_step P hrow x A t, ih]

lemma g72mab_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    g72mab_PS P x k y A ≤ g72mab_EX P x A k := by
  classical
  unfold g72mab_PS g72mab_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma g72mab_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, g72mab_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← g72mab_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => g72mab_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma g72mab_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → g72mab_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72mab_PS P x (s + 1) z (fun z => m + 1 < lev z) * g72mab_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [g72mab_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72mab_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then g72mab_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        g72mab_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * g72mab_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [g72mab_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72mab_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        g72mab_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          g72mab_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72mab_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          g72mab_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          g72mab_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          g72mab_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72mab_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [g72mab_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
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

lemma g72mab_cond_snoc {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma g72mab_PS_snoc (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72mab_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then g72mab_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold g72mab_PS
  rw [g72mab_tsum_snoc]
  simp_rw [g72mab_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := g72mab_cond_snoc x y A ω
    rw [g72mab_W_snoc]
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
lemma g72mab_conv3 (InvT mid A A' : V → Prop) [DecidablePred mid] (x : V) (hx : mid x)
    (hstep : ∀ w y, InvT y → P w y ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ InvT w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ L y, InvT y → g72mab_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) y A' else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [g72mab_PS_one]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, g72mab_PS_one]
    rw [tsum_eq_single x]
    · rw [if_pos hx, g72mab_PS_zero, if_pos rfl, one_mul]
    · intro z hz
      rw [g72mab_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ L ih =>
    intro y hy
    rw [Finset.sum_range_succ, g72mab_PS_snoc P x (L + 1)]
    have hlast : ∀ z, (if mid z then g72mab_PS P x (L + 1) z A *
        g72mab_PS P z (L + 1 + 1 - (L + 1)) y A' else 0) =
        if mid z then g72mab_PS P x (L + 1) z A * ENNReal.ofReal (P z y) else 0 := fun z => by
      rw [show L + 1 + 1 - (L + 1) = 1 by omega, g72mab_PS_one]
    simp_rw [hlast]
    have h1 : ∀ s ∈ Finset.range (L + 1), ∑' z, (if mid z then
        g72mab_PS P x s z A * g72mab_PS P z (L + 1 + 1 - s) y A' else 0) =
        ∑' w, (if A' w then ∑' z, (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
      intro s hs
      have hs' : s ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      have e : ∀ z, (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 + 1 - s) y A' else 0) =
          ∑' w, (if A' w then (if mid z then
          g72mab_PS P x s z A * g72mab_PS P z (L + 1 - s) w A' else 0) else 0) *
          ENNReal.ofReal (P w y) := by
        intro z
        rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, g72mab_PS_snoc P z (L + 1 - s)]
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

lemma g72mab_cauchy0 (a b : ℕ → ℝ≥0∞) :
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
section GRK
variable {V : Type*} (P : V → V → ℝ)

open Classical in
lemma g72mab_EX_eq (x : V) (A : V → Prop) (k : ℕ) :
    g72mab_EX P x A k = ∑' y, if ¬ A y then g72mab_PS P x k y A else 0 := by
  classical
  unfold g72mab_EX g72mab_PS
  simp_rw [g72mab_ite_tsum]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single (ω (Fin.last k))]
  · by_cases hA : A (ω (Fin.last k)) <;> simp [hA]
  · intro y hy; simp [Ne.symm hy]

open Classical in
lemma g72mab_AV_eq (x : V) (A : V → Prop) (k : ℕ) :
    g72mab_AV P x A (k + 1) = ∑' y, if A y then g72mab_PS P x (k + 1) y A else 0 := by
  classical
  unfold g72mab_AV g72mab_PS
  simp_rw [g72mab_ite_tsum]
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

lemma g72mab_PS_mono (A A' : V → Prop) (hAA : ∀ z, A z → A' z) (x y : V) (L : ℕ) :
    g72mab_PS P x L y A ≤ g72mab_PS P x L y A' := by
  classical
  unfold g72mab_PS
  refine ENNReal.tsum_le_tsum fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
  · rw [if_pos h, if_pos ⟨h.1, h.2.1, fun m h1 h2 => hAA _ (h.2.2 m h1 h2)⟩]
  · rw [if_neg h]; exact bot_le

lemma g72mab_PS_concat (A : V → Prop) (y z : V) (hy : A y) :
    ∀ u x t, g72mab_PS P x u y A * g72mab_PS P y t z A ≤ g72mab_PS P x (u + t) z A := by
  classical
  intro u
  induction u with
  | zero =>
    intro x t
    rw [g72mab_PS_zero, zero_add]
    split_ifs with h
    · subst h; rw [one_mul]
    · rw [zero_mul]; exact bot_le
  | succ u ih =>
    intro x t
    rw [g72mab_PS_cons P x u y A, show u + 1 + t = (u + t) + 1 by omega,
      g72mab_PS_cons P x (u + t) z A, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [mul_assoc]
    gcongr
    by_cases hw : A w
    · rw [if_pos (Or.inr hw), if_pos (Or.inr hw)]; exact ih w t
    · rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg (fun h => hw (by rw [h]; exact hy)), zero_mul]
        exact bot_le
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hw h]), zero_mul]; exact bot_le

lemma g72mab_taboo_extract (x0 y : V) (hy : y ≠ x0) (L : ℕ)
    (h : g72mab_PS P x0 L y (fun _ => True) ≠ 0) :
    ∃ u, g72mab_PS P x0 u y (fun z => z ≠ x0) ≠ 0 := by
  classical
  rcases L with _ | L
  · rw [g72mab_PS_zero, if_neg (Ne.symm hy)] at h; exact absurd rfl h
  rw [g72mab_conv3 P (fun _ => True) (fun z => z = x0) (fun _ => True) (fun z => z ≠ x0) x0 rfl
    (fun w _ _ _ => by by_cases hw : w = x0 <;> simp [hw]) L y trivial] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨z, hz⟩ : ∃ z, (if z = x0 then g72mab_PS P x0 s z (fun _ => True) *
      g72mab_PS P z (L + 1 - s) y (fun z => z ≠ x0) else 0) ≠ 0 := by
    by_contra hc; push Not at hc; exact hs (ENNReal.tsum_eq_zero.mpr hc)
  by_cases hzx : z = x0
  · rw [if_pos hzx] at hz
    subst hzx
    exact ⟨_, right_ne_zero_of_mul hz⟩
  · rw [if_neg hzx] at hz; exact absurd rfl hz

lemma g72mab_ofReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hne : ∑' a, ENNReal.ofReal (f a) ≠ ⊤) :
    ENNReal.ofReal (∑' a, f a) = ∑' a, ENNReal.ofReal (f a) := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf _)] using this
  exact ENNReal.ofReal_tsum_of_nonneg hf hs
end GRK

section TR
variable {V : Type*} [Countable V] [DecidableEq V]

lemma g72mab_qsum (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    HasSum (fun y => if y = x then 0 else Q x y) (holdRate Q x) := by
  have h := (hQ.2 x).sub (hasSum_ite_eq x (Q x x))
  have e : (fun y => if y = x then 0 else Q x y) = fun y => Q x y - (if y = x then Q x x else 0) := by
    funext y; by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  rw [e, show holdRate Q x = 0 - Q x x by simp [holdRate]]
  exact h

lemma g72mab_qge (Q : V → V → ℝ) (hQ : IsGenerator Q) (x y : V) (hxy : x ≠ y) :
    Q x y ≤ holdRate Q x := by
  have h := le_hasSum (g72mab_qsum Q hQ x) y (fun j hj => by
    split_ifs with h
    · exact le_rfl
    · exact hQ.1 x j (Ne.symm h))
  simpa [Ne.symm hxy] using h

lemma g72mab_jrow (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    ∑' y, ENNReal.ofReal (jumpP Q x y) = 1 := by
  classical
  unfold jumpP
  by_cases hq : holdRate Q x = 0
  · simp only [hq, if_true]
    rw [tsum_eq_single x]
    · simp
    · intro b hb; simp [hb]
  · simp only [hq, if_false]
    have hs := (g72mab_qsum Q hQ x).div_const (holdRate Q x)
    rw [div_self hq] at hs
    have hqpos : 0 < holdRate Q x := by
      have : 0 ≤ holdRate Q x := (g72mab_qsum Q hQ x).nonneg (fun j => by
        split_ifs with h
        · exact le_rfl
        · exact hQ.1 x j (Ne.symm h))
      exact lt_of_le_of_ne this (Ne.symm hq)
    have e : (fun y => (if y = x then 0 else Q x y) / holdRate Q x) =
        fun y => if y = x then 0 else Q x y / holdRate Q x := by
      funext y; split_ifs <;> simp
    rw [e] at hs
    have hnn : ∀ y, 0 ≤ (if y = x then (0 : ℝ) else Q x y / holdRate Q x) := fun y => by
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (hQ.1 x y (Ne.symm h)) hqpos.le
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs.summable, hs.tsum_eq, ENNReal.ofReal_one]

lemma g72mab_jpos (Q : V → V → ℝ) (hQ : IsGenerator Q) (x : V) :
    ∀ y, Relation.ReflTransGen (fun u v : V => u ≠ v ∧ 0 < Q u v) x y →
      ∃ L, g72mab_PS (jumpP Q) x L y (fun _ => True) ≠ 0 := by
  classical
  intro y h
  induction h with
  | refl => exact ⟨0, by rw [g72mab_PS_zero]; simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨L, hL⟩ := ih
    obtain ⟨hne, hpos⟩ := hbc
    have hq : 0 < holdRate Q b := lt_of_lt_of_le hpos (g72mab_qge Q hQ b c hne)
    have hj : 0 < jumpP Q b c := by
      unfold jumpP
      rw [if_neg hq.ne', if_neg (Ne.symm hne)]
      exact div_pos hpos hq
    refine ⟨L + 1, ?_⟩
    rw [g72mab_PS_snoc (jumpP Q) x L c (fun _ => True)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (if L = 0 ∨ True then g72mab_PS (jumpP Q) x L b (fun _ => True) else 0) *
          ENNReal.ofReal (jumpP Q b c) := by
          rw [if_pos (Or.inr trivial)]
          exact ENNReal.mul_pos hL (by simp [hj])
      _ ≤ _ := ENNReal.le_tsum b

lemma g72mab_rt (Q : V → V → ℝ) (x : V) (t : ℕ) :
    returnTail Q x t = g72mab_AV (jumpP Q) x (fun z => z ≠ x) t := by
  unfold returnTail g72mab_AV
  refine tsum_congr fun ω => ?_
  split_ifs <;> rfl

lemma g72mab_exsum (Q : V → V → ℝ) (hQ : IsGenerator Q) (x0 y : V) (hyx : y ≠ x0)
    (hirr : IsIrreducibleGen Q) (hrec : RecurrentState Q x0) :
    ∑' t, g72mab_EX (jumpP Q) y (fun z => z ≠ x0) (t + 1) = 1 := by
  classical
  set P := jumpP Q with hPd
  have hrow : ∀ z, ∑' w, ENNReal.ofReal (P z w) = 1 := g72mab_jrow Q hQ
  set A : V → Prop := fun z => z ≠ x0 with hA
  have hmass := g72mab_mass P hrow y A
  have hSle : ∑' t, g72mab_EX P y A (t + 1) ≤ 1 :=
    ENNReal.tsum_le_of_sum_range_le fun t => by rw [← hmass t]; exact le_add_self
  by_contra hne
  have hlt : ∑' t, g72mab_EX P y A (t + 1) < 1 := lt_of_le_of_ne hSle hne
  set S := ∑' t, g72mab_EX P y A (t + 1) with hSd
  have hq : 0 < 1 - S := tsub_pos_of_lt hlt
  have hAV : ∀ t, 1 - S ≤ g72mab_AV P y A t := by
    intro t
    refine tsub_le_iff_right.mpr ?_
    calc (1 : ℝ≥0∞) = g72mab_AV P y A t + ∑ k ∈ Finset.range t, g72mab_EX P y A (k + 1) :=
          (hmass t).symm
      _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum _
  obtain ⟨s, hs⟩ := g72mab_jpos Q hQ x0 y (hirr x0 y)
  obtain ⟨u, hu⟩ := g72mab_taboo_extract P x0 y hyx s hs
  set c := g72mab_PS P x0 u y (fun z => z ≠ x0) with hc
  have hlow : ∀ t, c * (1 - S) ≤ returnTail Q x0 (u + (t + 1)) := by
    intro t
    calc c * (1 - S) ≤ c * g72mab_AV P y A (t + 1) := by gcongr; exact hAV (t + 1)
      _ = ∑' z, c * (if A z then g72mab_PS P y (t + 1) z A else 0) := by
          rw [g72mab_AV_eq, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
      _ ≤ ∑' z, if A z then g72mab_PS P x0 (u + (t + 1)) z A else 0 := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : A z
          · rw [if_pos hz, if_pos hz]
            exact g72mab_PS_concat P A y z hyx u x0 (t + 1)
          · rw [if_neg hz, mul_zero]; exact bot_le
      _ = _ := by
          rw [g72mab_rt, show u + (t + 1) = (u + t) + 1 by omega, g72mab_AV_eq]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
  have hlim : Filter.Tendsto (fun t => returnTail Q x0 (u + (t + 1))) Filter.atTop (nhds 0) :=
    hrec.comp (Filter.tendsto_atTop_mono (fun t => (by omega : t ≤ u + (t + 1)))
      Filter.tendsto_id)
  have h0 : c * (1 - S) ≤ 0 := ge_of_tendsto' hlim hlow
  have hpos : 0 < c * (1 - S) := ENNReal.mul_pos hu hq.ne'
  exact absurd h0 (not_le.mpr hpos)
end TR

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (T : TreeData ι) (hT : IsTreeProcess T)
    (hrec : IsRecurrentProcess (gen T)) :
    ∀ i : ι, ∑' j : ι, matN T i j * ENNReal.ofReal (T.d j) = 1 := by
  classical
  intro i
  obtain ⟨hgen, hirr⟩ := hT
  have hex := g72mab_exsum (gen T) hgen none (some ([], i)) (by simp) hirr (hrec none)
  set Q := gen T with hQd
  set P := jumpP Q with hPd
  set A : TreeState ι → Prop := fun z => z ≠ none with hA
  set y : TreeState ι := some ([], i) with hy
  have hyx : y ≠ none := by simp [hy]
  rw [← hex]
  have hEX : ∀ t, g72mab_EX P y A (t + 1) = g72mab_PS P y (t + 1) none A := by
    intro t
    rw [g72mab_EX_eq, tsum_eq_single none]
    · simp [hA]
    · intro z hz; simp [hA, hz]
  simp_rw [hEX]
  have hd : ∀ (j : ι), T.d j = Q (some ([], j)) none := by intro j; simp [hQd, gen]
  have hfac : ∀ j, ENNReal.ofReal ((holdRate Q (some ([], j)))⁻¹) * ENNReal.ofReal (T.d j) =
      ENNReal.ofReal (P (some ([], j)) none) := by
    intro j
    have hdnn : 0 ≤ T.d j := by rw [hd]; exact hgen.1 _ _ (by simp)
    simp only [hPd, jumpP]
    by_cases hq : holdRate Q (some ([], j)) = 0
    · simp [hq]
    · rw [if_neg hq, if_neg (by simp), ← hd]
      by_cases hqn : 0 ≤ (holdRate Q (some ([], j)))⁻¹
      · rw [← ENNReal.ofReal_mul hqn, div_eq_mul_inv, mul_comm]
      · push Not at hqn
        rw [ENNReal.ofReal_of_nonpos hqn.le, zero_mul, ENNReal.ofReal_of_nonpos]
        rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos hdnn hqn.le
  have hN : ∀ j, matN T i j = (∑' t, g72mab_PS P y t (some ([], j)) A) *
      ENNReal.ofReal ((holdRate Q (some ([], j)))⁻¹) := by
    intro j
    unfold matN sojournAvoid
    congr 1
    unfold expVisitsAvoid g72mab_PS
    refine tsum_congr fun t => tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2
      exact ⟨h1.1, h1.2.1, fun m hm _ => by simpa [hA] using h1.2.2 m hm⟩
    · exfalso; apply h1
      refine ⟨h2.1, h2.2.1, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2.2.1]; simp
      · simpa [hA] using h2.2.2 m hm hl
    · rfl
  simp_rw [hN, mul_assoc, hfac]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun t => ?_
  rw [g72mab_PS_snoc P y t none A]
  have hinj : Function.Injective (fun j : ι => (some ([], j) : TreeState ι)) := by
    intro a b h; simpa using h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun j => ?_
    rw [if_pos (Or.inr (by simp [hA]))]
  · intro z hz
    rw [Function.mem_support] at hz
    rcases z with _ | ⟨l, k⟩
    · exfalso; apply hz
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht; rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg hyx]; simp
      · rw [if_neg (by rintro (h | h) <;> [omega; exact h rfl])]; simp
    · by_cases hl : l = []
      · subst hl; exact ⟨k, rfl⟩
      · exfalso; apply hz
        have : P (some (l, k)) none = 0 := by
          simp only [hPd, jumpP]
          by_cases hq : holdRate Q (some (l, k)) = 0 <;> simp [hq, hQd, gen, hl]
        simp [this]
