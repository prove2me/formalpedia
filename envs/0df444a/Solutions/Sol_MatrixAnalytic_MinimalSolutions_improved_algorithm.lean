-- Prove2me | solution 1 for MatrixAnalytic.MinimalSolutions.improved_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:14:42.084925+00:00
-- url     : https://prove2.me/submissions/8f2bc9b4-dda1-4a41-abfd-d6dbf3c2da7e

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Improved

open scoped ENNReal

namespace S202IA
open MatrixAnalytic.MinimalSolutions

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

section QBDm
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma g72mab_qnz (x w : ℕ × ι) (h : qbdP B A₀ A₁ A₂ x w ≠ 0) : w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 := by
  unfold qbdP at h
  split_ifs at h <;> first | omega | exact absurd rfl h

omit [Countable ι] [DecidableEq ι] in
lemma g72mab_qshiftN (a b : ℕ) (i j : ι) (ha : 1 ≤ a) :
    qbdP B A₀ A₁ A₂ (a + 1, i) (b + 1, j) = qbdP B A₀ A₁ A₂ (a, i) (b, j) := by
  unfold qbdP; simp only; split_ifs <;> first | rfl | (exfalso; omega)

def g72mab_sh {L : ℕ} (ω : Fin (L + 1) → ℕ × ι) : Fin (L + 1) → ℕ × ι :=
  fun s => ((ω s).1 + 1, (ω s).2)

omit [Countable ι] [DecidableEq ι] in
lemma g72mab_sh_inj {L : ℕ} : Function.Injective (g72mab_sh (ι := ι) (L := L)) := by
  intro ω ω' h
  funext s
  have := congrFun h s
  simp only [g72mab_sh, Prod.mk.injEq] at this
  exact Prod.ext (by omega) this.2

lemma g72mab_PS_shiftN (n a b : ℕ) (i j : ι) (ha : 1 ≤ a) (L : ℕ) :
    g72mab_PS (qbdP B A₀ A₁ A₂) (a + 1, i) L (b + 1, j) (fun z => n + 1 < z.1) =
      g72mab_PS (qbdP B A₀ A₁ A₂) (a, i) L (b, j) (fun z => n < z.1) := by
  classical
  unfold g72mab_PS
  rw [← g72mab_sh_inj.tsum_eq]
  · refine tsum_congr fun ω => ?_
    have hc : ((g72mab_sh ω) 0 = (a + 1, i) ∧ (g72mab_sh ω) (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < ((g72mab_sh ω) m).1) ↔
        (ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1) := by
      simp only [g72mab_sh, Prod.ext_iff, add_left_inj, Nat.add_lt_add_iff_right]
    by_cases h : ω 0 = (a, i) ∧ ω (Fin.last L) = (b, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n < (ω m).1
    · rw [if_pos (hc.mpr h), if_pos h]
      unfold g72mab_W
      refine Finset.prod_congr rfl fun s _ => ?_
      have hl : 1 ≤ (ω s.castSucc).1 := by
        by_cases hs : s.castSucc = 0
        · rw [hs, h.1]; exact ha
        · have := h.2.2 s.castSucc hs (Fin.castSucc_ne_last s); omega
      simp only [g72mab_sh]
      rw [g72mab_qshiftN B A₀ A₁ A₂ _ _ _ _ hl]
    · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]
  · intro ω hω
    rw [Function.mem_support] at hω
    have hcond : ω 0 = (a + 1, i) ∧ ω (Fin.last L) = (b + 1, j) ∧
        ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → n + 1 < (ω m).1 := by
      by_contra hn; exact hω (if_neg hn)
    refine ⟨fun s => ((ω s).1 - 1, (ω s).2), funext fun s => ?_⟩
    have : 1 ≤ (ω s).1 := by
      by_cases h0 : s = 0
      · rw [h0, hcond.1]; omega
      by_cases hl : s = Fin.last L
      · rw [hl, hcond.2.1]; omega
      have := hcond.2.2 s h0 hl; omega
    simp only [g72mab_sh]
    exact Prod.ext (by simp; omega) rfl

end QBDm

lemma g72mab_levn {ι : Type*} (n : ℕ) (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = n then f z else 0) = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]

lemma g72mab_swap0 {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact g72mab_cauchy0 (a z) (b z)
  · simp [hz]

lemma g72mab_mm_assoc {ι : Type*} [Countable ι] (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE (matMulE X Y) Z = matMulE X (matMulE Y Z) := by
  funext i j
  unfold matMulE
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  ring

lemma g72mab_mm_one {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) :
    matMulE X matOneE = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

lemma g72mab_pow_succ' {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) (m : ℕ) :
    matMulE X (matPowE X m) = matPowE X (m + 1) := by
  induction m with
  | zero =>
    show matMulE X matOneE = matMulE matOneE X
    rw [g72mab_mm_one]
    funext i j
    unfold matMulE matOneE
    rw [tsum_eq_single i]
    · simp
    · intro b hb; simp [Ne.symm hb]
  | succ m ih =>
    show matMulE X (matMulE (matPowE X m) X) = matMulE (matPowE X (m + 1)) X
    rw [← g72mab_mm_assoc, ih]


section UGRgen
variable {V : Type*} (P : V → V → ℝ)

lemma g72mab_PS_congr (I A A' : V → Prop) (y : V)
    (hstep : ∀ w z, I w → P w z ≠ 0 → (A z ↔ A' z) ∧ (A z → I z)) :
    ∀ L x, I x → g72mab_PS P x L y A = g72mab_PS P x L y A' := by
  classical
  intro L
  induction L with
  | zero => intro x _; rw [g72mab_PS_zero, g72mab_PS_zero]
  | succ L ih =>
    intro x hx
    rw [g72mab_PS_cons P x L y A, g72mab_PS_cons P x L y A']
    refine tsum_congr fun z => ?_
    by_cases hP0 : P x z = 0
    · simp [hP0]
    obtain ⟨hiff, hI⟩ := hstep x z hx hP0
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp only [true_or, if_true, g72mab_PS_zero]
    · by_cases hz : A z
      · rw [if_pos (Or.inr hz), if_pos (Or.inr (hiff.mp hz)), ih z (hI hz)]
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hz h]),
          if_neg (by rintro (h | h) <;> [omega; exact hz (hiff.mpr h)])]

lemma g72mab_partial (a b : ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) ≤
      (∑ s ∈ Finset.range T, a s) * ∑' u, b u := by
  classical
  set a' : ℕ → ℝ≥0∞ := fun s => if s < T then a s else 0 with ha'
  have e1 : ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a s * b (t - s) =
      ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), a' s * b (t - s) := by
    refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun s hs => ?_
    have : s < T := by
      have := Finset.mem_range.mp ht; have := Finset.mem_range.mp hs; omega
    simp [ha', this]
  have e2 : ∑' s, a' s = ∑ s ∈ Finset.range T, a s := by
    rw [tsum_eq_sum (s := Finset.range T)]
    · exact Finset.sum_congr rfl fun s hs => by simp [ha', Finset.mem_range.mp hs]
    · intro s hs; simp [ha', Finset.mem_range.not.mp hs]
  rw [e1, ← e2, ← g72mab_cauchy0]
  exact ENNReal.sum_le_tsum _

lemma g72mab_swapT {W : Type*} (mid : W → Prop) [DecidablePred mid] (a : W → ℕ → ℝ≥0∞)
    (b : W → ℕ → ℝ≥0∞) (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ s ∈ Finset.range (t + 1), ∑' z, (if mid z then a z s * b z (t - s) else 0) ≤
      ∑' z, if mid z then (∑ s ∈ Finset.range T, a z s) * ∑' u, b z u else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact g72mab_partial (a z) (b z) T
  · simp [hz]

lemma g72mab_seriesInv {ι : Type*} [Countable ι] [DecidableEq ι] (U N : ι → ι → ℝ≥0∞)
    (f : ι → ι → ℕ → ℝ≥0∞) (hNf : ∀ i j, N i j = ∑' t, f i j t)
    (hNeq : ∀ i j, N i j = matOneE i j + ∑' l, N i l * U l j)
    (hpart : ∀ T i j, ∑ t ∈ Finset.range (T + 1), f i j t ≤
      matOneE i j + ∑' l, (∑ t ∈ Finset.range T, f i l t) * U l j) :
    N = seriesInvE U := by
  have hS : ∀ i j, seriesInvE U i j = matOneE i j + ∑' l, seriesInvE U i l * U l j := by
    intro i j
    unfold seriesInvE
    rw [tsum_eq_zero_add' ENNReal.summable]
    congr 1
    show ∑' ν, matMulE (matPowE U ν) U i j = _
    unfold matMulE
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_right]
  have h1 : ∀ T i j, ∑ t ∈ Finset.range T, f i j t ≤ seriesInvE U i j := by
    intro T
    induction T with
    | zero => intro i j; simp
    | succ T ih =>
      intro i j
      refine (hpart T i j).trans ?_
      rw [hS i j]
      gcongr with l
      exact ih i l
  have h2 : ∀ K i j, ∑ ν ∈ Finset.range K, matPowE U ν i j ≤ N i j := by
    intro K
    induction K with
    | zero => intro i j; simp
    | succ K ih =>
      intro i j
      rw [Finset.sum_range_succ', hNeq i j, add_comm]
      gcongr
      · exact le_of_eq rfl
      · show ∑ ν ∈ Finset.range K, ∑' l, matPowE U ν i l * U l j ≤ _
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine ENNReal.tsum_le_tsum fun l => ?_
        rw [← Finset.sum_mul]
        gcongr
        exact ih i l
  funext i j
  refine le_antisymm ?_ ?_
  · rw [hNf i j, ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun T => h1 T i j
  · unfold seriesInvE
    rw [ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun K => h2 K i j
end UGRgen
section UGRq
variable {ι : Type*} [Countable ι] [DecidableEq ι]

lemma g72mab_fe (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) (hy : y ∈ T) :
    firstEntrance P T x y = ∑' t, g72mab_PS P x (t + 1) y (fun z => z ∉ T) := by
  classical
  unfold firstEntrance g72mab_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 1 + 1), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
  · rw [if_pos ⟨h.1, h.2.1, hy, h.2.2⟩, if_pos h]; rfl
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1, h'.2.2.2⟩), if_neg h]
end UGRq

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

lemma g72mab_stepPow_nonneg {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; simp only [stepPow]; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hP0 _ _)

lemma g72mab_stepPow_PS {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) (x : V) :
    ∀ t y, 0 < stepPow P t x y → g72mab_PS P x t y (fun _ => True) ≠ 0 := by
  classical
  intro t
  induction t with
  | zero =>
    intro y h
    simp only [stepPow] at h
    rw [g72mab_PS_zero]
    split_ifs at h with hxy
    · simp [hxy]
    · norm_num at h
  | succ t ih =>
    intro y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, stepPow P t x z * P z y ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [tsum_congr hc, tsum_zero] at h
      exact lt_irrefl _ h
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne (g72mab_stepPow_nonneg P hP0 t x z) (Ne.symm (left_ne_zero_of_mul hz))
    have h2 : 0 < P z y := lt_of_le_of_ne (hP0 z y) (Ne.symm (right_ne_zero_of_mul hz))
    rw [g72mab_PS_snoc P x t y (fun _ => True)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < (if t = 0 ∨ True then g72mab_PS P x t z (fun _ => True) else 0) *
          ENNReal.ofReal (P z y) := by
          rw [if_pos (Or.inr trivial)]
          exact ENNReal.mul_pos (ih z h1) (by simp [h2])
      _ ≤ _ := ENNReal.le_tsum z

lemma g72mab_G_sum {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x) (i : ι) :
    ∑' j, matG (qbdP B A₀ A₁ A₂) i j = 1 := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP.1
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hP.2 z).summable, (hP.2 z).tsum_eq,
      ENNReal.ofReal_one]
  set A : ℕ × ι → Prop := fun z => z ∉ (level 0 : Set (ℕ × ι)) with hA
  set y : ℕ × ι := (1, i) with hy
  set x0 : ℕ × ι := (0, i) with hx0
  have hS : ∑' j, matG P i j = ∑' t, g72mab_EX P y A (t + 1) := by
    have : ∀ j, matG P i j = ∑' t, g72mab_PS P y (t + 1) (0, j) A := fun j =>
      g72mab_fe P _ _ _ (by simp [level])
    simp_rw [this, g72mab_EX_eq]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun t => ?_
    symm
    calc _ = ∑' z : ℕ × ι, (if z.1 = 0 then g72mab_PS P y (t + 1) z A else 0) :=
          tsum_congr fun z => by split_ifs <;> simp_all [hA, level]
      _ = _ := g72mab_levn 0 _
  have hmass := g72mab_mass P hrow y A
  have hSle : ∑' t, g72mab_EX P y A (t + 1) ≤ 1 :=
    ENNReal.tsum_le_of_sum_range_le fun t => by rw [← hmass t]; exact le_add_self
  rw [hS]
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
  obtain ⟨s, hs⟩ := hirr x0 y
  have hyx0 : y ≠ x0 := by simp [hy, hx0]
  obtain ⟨u, hu⟩ := g72mab_taboo_extract P x0 y hyx0 s (g72mab_stepPow_PS P hP0 x0 s y hs)
  set c := g72mab_PS P x0 u y (fun z => z ≠ x0) with hc
  have hconv : ∀ T, ENNReal.ofReal (returnTailC P x0 T) =
      g72mab_AV P x0 (fun z => z ≠ x0) T := by
    intro T
    have hAVle : g72mab_AV P x0 (fun z => z ≠ x0) T ≤ 1 :=
      le_self_add.trans_eq (g72mab_mass P hrow x0 _ T)
    unfold returnTailC setAvoidTailC
    rw [g72mab_ofReal_tsum]
    · unfold g72mab_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC g72mab_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
    · intro ω; split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    · refine ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_of_eq ?_) hAVle)
      unfold g72mab_AV
      refine tsum_congr fun ω => ?_
      split_ifs with h1 h2 h2
      · unfold pathWeightC g72mab_W
        exact ENNReal.ofReal_prod_of_nonneg fun s _ => hP0 _ _
      · exact absurd ⟨h1.1, fun i hi => by simpa using h1.2 i hi⟩ h2
      · exact absurd ⟨h2.1, fun i hi => by simpa using h2.2 i hi⟩ h1
      · simp
  have hAx : ∀ w, A w → w ≠ x0 := by
    intro w hw h; rw [h] at hw; exact hw (by simp [level, hx0])
  have hlow : ∀ t, c * (1 - S) ≤ ENNReal.ofReal (returnTailC P x0 (u + (t + 1))) := by
    intro t
    calc c * (1 - S) ≤ c * g72mab_AV P y A (t + 1) := by gcongr; exact hAV (t + 1)
      _ = ∑' z, c * (if A z then g72mab_PS P y (t + 1) z A else 0) := by
          rw [g72mab_AV_eq, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
      _ ≤ ∑' z, if z ≠ x0 then g72mab_PS P x0 (u + (t + 1)) z (fun z => z ≠ x0) else 0 := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hz : A z
          · rw [if_pos hz, if_pos (hAx z hz)]
            calc c * g72mab_PS P y (t + 1) z A ≤
                c * g72mab_PS P y (t + 1) z (fun z => z ≠ x0) := by
                  gcongr; exact g72mab_PS_mono P _ _ hAx _ _ _
              _ ≤ _ := g72mab_PS_concat P (fun z => z ≠ x0) y z hyx0 u x0 (t + 1)
          · rw [if_neg hz, mul_zero]; exact bot_le
      _ = _ := by
          rw [hconv, show u + (t + 1) = (u + t) + 1 by omega, g72mab_AV_eq]
          refine tsum_congr fun z => ?_
          split_ifs <;> rfl
  have hlim : Filter.Tendsto (fun t => ENNReal.ofReal (returnTailC P x0 (u + (t + 1))))
      Filter.atTop (nhds 0) := by
    have h1 := ENNReal.tendsto_ofReal (hrec x0)
    rw [ENNReal.ofReal_zero] at h1
    exact h1.comp (Filter.tendsto_atTop_mono (fun t => (by omega : t ≤ u + (t + 1)))
      Filter.tendsto_id)
  have h0 : c * (1 - S) ≤ 0 := ge_of_tendsto' hlim hlow
  have hpos : 0 < c * (1 - S) := ENNReal.mul_pos hu hq.ne'
  exact absurd h0 (not_le.mpr hpos)

open Matrix

section Real
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- level vectors of the truncated chain -/
noncomputable def Hs (A₀ A₁ A₂ : Matrix ι ι ℝ) (k : ℕ) (a b : ι → ℝ) : ℕ → ι → ℝ
  | 0 => a
  | 1 => b
  | (p + 2) => Gbar A₀ A₁ A₂ (k - p - 1) *ᵥ Hs A₀ A₁ A₂ k a b (p + 1)

variable (A₀ A₁ A₂ : Matrix ι ι ℝ)

lemma Hs_two_add (k : ℕ) (a b : ι → ℝ) (p : ℕ) :
    Hs A₀ A₁ A₂ k a b (p + 2) = Gbar A₀ A₁ A₂ (k - p - 1) *ᵥ Hs A₀ A₁ A₂ k a b (p + 1) := by
  rw [Hs]

lemma Gbar_succ (m : ℕ) : Gbar A₀ A₁ A₂ (m + 1) = (1 - Ubar A₀ A₁ A₂ (m + 1))⁻¹ * A₂ := rfl

lemma Ubar_succ (m : ℕ) : Ubar A₀ A₁ A₂ (m + 1) = A₁ + A₀ * Gbar A₀ A₁ A₂ m := rfl

lemma Hs_harm (k : ℕ) (a b : ι → ℝ)
    (hG : ∀ m, 1 ≤ m → m < k → (1 - Ubar A₀ A₁ A₂ m) * Gbar A₀ A₁ A₂ m = A₂)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hk : ℓ ≤ k) :
    Hs A₀ A₁ A₂ k a b ℓ = A₀ *ᵥ Hs A₀ A₁ A₂ k a b (ℓ + 1) + A₁ *ᵥ Hs A₀ A₁ A₂ k a b ℓ +
      A₂ *ᵥ Hs A₀ A₁ A₂ k a b (ℓ - 1) := by
  obtain ⟨p, rfl⟩ : ∃ p, ℓ = p + 2 := ⟨ℓ - 2, by omega⟩
  obtain ⟨m', hm'⟩ : ∃ m', k - p - 1 = m' + 1 := ⟨k - p - 2, by omega⟩
  have e1 : Hs A₀ A₁ A₂ k a b (p + 2) =
      Gbar A₀ A₁ A₂ (m' + 1) *ᵥ Hs A₀ A₁ A₂ k a b (p + 1) := by
    rw [Hs_two_add, hm']
  have e2 : Hs A₀ A₁ A₂ k a b (p + 2 + 1) =
      Gbar A₀ A₁ A₂ m' *ᵥ Hs A₀ A₁ A₂ k a b (p + 2) := by
    rw [show p + 2 + 1 = (p + 1) + 2 by omega, Hs_two_add]
    congr 2; omega
  have hGm := hG (m' + 1) (by omega) (by omega)
  have key : (1 - Ubar A₀ A₁ A₂ (m' + 1)) *ᵥ Hs A₀ A₁ A₂ k a b (p + 2) =
      A₂ *ᵥ Hs A₀ A₁ A₂ k a b (p + 1) := by
    rw [e1, Matrix.mulVec_mulVec, hGm]
  rw [Ubar_succ, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    ← e2] at key
  rw [show p + 2 - 1 = p + 1 by omega, ← key]
  abel

lemma Hs_harm1 (k : ℕ) (hk : 1 ≤ k) (a b : ι → ℝ)
    (hb : (1 - Ubar A₀ A₁ A₂ k) *ᵥ b = A₂ *ᵥ a) :
    Hs A₀ A₁ A₂ k a b 1 = A₀ *ᵥ Hs A₀ A₁ A₂ k a b (1 + 1) + A₁ *ᵥ Hs A₀ A₁ A₂ k a b 1 +
      A₂ *ᵥ Hs A₀ A₁ A₂ k a b (1 - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have e2 : Hs A₀ A₁ A₂ (k' + 1) a b (1 + 1) = Gbar A₀ A₁ A₂ k' *ᵥ b := by
    rw [show (1 + 1 : ℕ) = 0 + 2 from rfl, Hs_two_add]
    congr 2
  rw [Ubar_succ, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec] at hb
  rw [e2]
  show b = A₀ *ᵥ (Gbar A₀ A₁ A₂ k' *ᵥ b) + A₁ *ᵥ b + A₂ *ᵥ a
  rw [← hb]
  abel

lemma Hs_top (k : ℕ) (hk : 1 ≤ k) (a b : ι → ℝ) :
    Hs A₀ A₁ A₂ k a b (k + 1) = Hs A₀ A₁ A₂ k a b k := by
  obtain ⟨p, rfl⟩ : ∃ p, k = p + 1 := ⟨k - 1, by omega⟩
  rw [show p + 1 + 1 = p + 2 by omega, Hs_two_add, show p + 1 - p - 1 = 0 by omega]
  show (1 : Matrix ι ι ℝ) *ᵥ _ = _
  rw [Matrix.one_mulVec]

lemma Hs_nonneg (k : ℕ) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hGn : ∀ m i j, 0 ≤ Gbar A₀ A₁ A₂ m i j) : ∀ ℓ i, 0 ≤ Hs A₀ A₁ A₂ k a b ℓ i := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro i
    match ℓ, ih with
    | 0, _ => exact ha i
    | 1, _ => exact hb i
    | p + 2, ih =>
      rw [Hs_two_add]
      exact Finset.sum_nonneg fun q _ => mul_nonneg (hGn _ _ _) (ih (p + 1) (by omega) q)

end Real

section Reach
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stepPow_nonneg' {V : Type*} [Countable V] [DecidableEq V] (P : V → V → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y; simp only [stepPow]; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hP0 _ _)

lemma reach (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP0 : ∀ x y, 0 ≤ qbdP B A₀ A₁ A₂ x y)
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (k : ℕ) (Good : ℕ → ι → Prop)
    (c0 : ∀ ℓ p q, Good ℓ p → 0 < A₀ p q → Good (min (ℓ + 1) k) q)
    (c1 : ∀ ℓ p q, Good ℓ p → 0 < A₁ p q → Good ℓ q)
    (c2 : ∀ ℓ p q, Good ℓ p → 0 < A₂ p q → 2 ≤ ℓ ∧ Good (ℓ - 1) q)
    (cg : ∀ ℓ p, Good ℓ p → 1 ≤ ℓ) (ℓ0 : ℕ) (p0 : ι) (hg : Good ℓ0 p0) : False := by
  set P := qbdP B A₀ A₁ A₂ with hPd
  have key : ∀ t y, 0 < stepPow P t (ℓ0, p0) y → ∃ m, m ≤ y.1 ∧ Good m y.2 := by
    intro t
    induction t with
    | zero =>
      intro y h
      simp only [stepPow] at h
      split_ifs at h with hy
      · subst hy; exact ⟨ℓ0, le_rfl, hg⟩
      · exact absurd h (lt_irrefl _)
    | succ t ih =>
      intro y h
      simp only [stepPow] at h
      obtain ⟨z, hz⟩ : ∃ z, stepPow P t (ℓ0, p0) z * P z y ≠ 0 := by
        by_contra hc
        push Not at hc
        rw [tsum_congr hc, tsum_zero] at h
        exact lt_irrefl _ h
      have h1 : 0 < stepPow P t (ℓ0, p0) z :=
        lt_of_le_of_ne (stepPow_nonneg' P hP0 t _ z) (Ne.symm (left_ne_zero_of_mul hz))
      have h2 : 0 < P z y := lt_of_le_of_ne (hP0 z y) (Ne.symm (right_ne_zero_of_mul hz))
      obtain ⟨m, hm, hgm⟩ := ih z h1
      have hm1 := cg m _ hgm
      obtain ⟨n, i⟩ := z
      obtain ⟨n', j⟩ := y
      simp only at hm hgm ⊢
      have hn : n ≠ 0 := by omega
      simp only [hPd, qbdP, hn, if_false] at h2
      split_ifs at h2 with e1 e2 e3
      · exact ⟨min (m + 1) k, by omega, c0 m i j hgm h2⟩
      · exact ⟨m, by omega, c1 m i j hgm h2⟩
      · obtain ⟨hm2, hg'⟩ := c2 m i j hgm h2
        exact ⟨m - 1, by omega, hg'⟩
      · exact absurd h2 (lt_irrefl _)
  obtain ⟨t, ht⟩ := hirr (ℓ0, p0) (0, p0)
  obtain ⟨m, hm, hgm⟩ := key t _ ht
  have := cg m _ hgm
  simp only at hm
  omega

lemma maxP (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP0 : ∀ x y, 0 ≤ qbdP B A₀ A₁ A₂ x y)
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (h0 : ∀ i j, 0 ≤ A₀ i j) (h1 : ∀ i j, 0 ≤ A₁ i j) (h2 : ∀ i j, 0 ≤ A₂ i j)
    (hrow : ∀ i, ∑ q, (A₀ i q + A₁ i q + A₂ i q) = 1)
    (k : ℕ) (hk : 1 ≤ k) (H : ℕ → ι → ℝ) (H0 : ∀ q, H 0 q ≤ 0) (Htop : H (k + 1) = H k)
    (Hh : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ i,
      H ℓ i ≤ (A₀ *ᵥ H (ℓ + 1)) i + (A₁ *ᵥ H ℓ) i + (A₂ *ᵥ H (ℓ - 1)) i) :
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ i, H ℓ i ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ℓ0, hl1, hl2, i0, hpos⟩ := hcon
  set s : Finset (ℕ × ι) := Finset.Icc 1 k ×ˢ Finset.univ with hs
  obtain ⟨⟨ℓs, is⟩, hmem, hmax⟩ := s.exists_max_image (fun x => H x.1 x.2)
    ⟨(ℓ0, i0), by simp [hs]; omega⟩
  simp only [hs, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true] at hmem
  set M := H ℓs is with hM
  have hMpos : 0 < M := lt_of_lt_of_le hpos (hmax (ℓ0, i0) (by simp [hs]; omega))
  have hle : ∀ ℓ, ℓ ≤ k + 1 → ∀ q, H ℓ q ≤ M := by
    intro ℓ hℓ q
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · subst h; linarith [H0 q]
    by_cases hℓk : ℓ = k + 1
    · subst hℓk; rw [Htop]; exact hmax (k, q) (by simp [hs]; omega)
    · exact hmax (ℓ, q) (by simp [hs]; omega)
  set Good : ℕ → ι → Prop := fun ℓ p => 1 ≤ ℓ ∧ ℓ ≤ k ∧ H ℓ p = M with hGood
  have clos : ∀ ℓ p, Good ℓ p → ∀ q,
      A₀ p q * (M - H (ℓ + 1) q) = 0 ∧ A₁ p q * (M - H ℓ q) = 0 ∧
        A₂ p q * (M - H (ℓ - 1) q) = 0 := by
    intro ℓ p ⟨g1, g2, g3⟩
    set r : ι → ℝ := fun q => A₀ p q * (M - H (ℓ + 1) q) + A₁ p q * (M - H ℓ q) +
      A₂ p q * (M - H (ℓ - 1) q) with hr
    have n0 : ∀ q, 0 ≤ A₀ p q * (M - H (ℓ + 1) q) := fun q =>
      mul_nonneg (h0 _ _) (by linarith [hle (ℓ + 1) (by omega) q])
    have n1 : ∀ q, 0 ≤ A₁ p q * (M - H ℓ q) := fun q =>
      mul_nonneg (h1 _ _) (by linarith [hle ℓ (by omega) q])
    have n2 : ∀ q, 0 ≤ A₂ p q * (M - H (ℓ - 1) q) := fun q =>
      mul_nonneg (h2 _ _) (by linarith [hle (ℓ - 1) (by omega) q])
    have hsum : ∑ q, r q = M - ((A₀ *ᵥ H (ℓ + 1)) p + (A₁ *ᵥ H ℓ) p + (A₂ *ᵥ H (ℓ - 1)) p) := by
      have : ∀ q, r q = M * (A₀ p q + A₁ p q + A₂ p q) -
          (A₀ p q * H (ℓ + 1) q + A₁ p q * H ℓ q + A₂ p q * H (ℓ - 1) q) := fun q => by
        simp only [hr]; ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, mul_one,
        Matrix.mulVec, dotProduct, Finset.sum_add_distrib]
    have hle0 : ∑ q, r q ≤ 0 := by
      rw [hsum]; have := Hh ℓ g1 g2 p; rw [g3] at this; linarith
    have hz : ∀ q ∈ Finset.univ, r q = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun q _ => by
        simp only [hr]; linarith [n0 q, n1 q, n2 q]).mp (le_antisymm hle0
          (Finset.sum_nonneg fun q _ => by simp only [hr]; linarith [n0 q, n1 q, n2 q]))
    intro q
    have := hz q (Finset.mem_univ _)
    simp only [hr] at this
    refine ⟨?_, ?_, ?_⟩ <;> linarith [n0 q, n1 q, n2 q]
  refine reach B A₀ A₁ A₂ hP0 hirr k Good ?_ ?_ ?_ (fun ℓ p g => g.1) ℓs is
    ⟨hmem.1, hmem.2, rfl⟩
  · intro ℓ p q g hq
    have e := (clos ℓ p g q).1
    have : H (ℓ + 1) q = M := by
      rcases mul_eq_zero.mp e with h | h
      · linarith
      · linarith
    by_cases hlk : ℓ + 1 ≤ k
    · rw [min_eq_left hlk]; exact ⟨by omega, hlk, this⟩
    · have hl : ℓ = k := by have := g.2.1; omega
      rw [min_eq_right (by omega)]
      subst hl
      exact ⟨hk, le_rfl, by rw [← Htop]; exact this⟩
  · intro ℓ p q g hq
    have e := (clos ℓ p g q).2.1
    have : H ℓ q = M := by
      rcases mul_eq_zero.mp e with h | h
      · linarith
      · linarith
    exact ⟨g.1, g.2.1, this⟩
  · intro ℓ p q g hq
    have e := (clos ℓ p g q).2.2
    have : H (ℓ - 1) q = M := by
      rcases mul_eq_zero.mp e with h | h
      · linarith
      · linarith
    have hl2 : 2 ≤ ℓ := by
      by_contra hl
      have h0' : ℓ - 1 = 0 := by omega
      have h3 := H0 q
      rw [← h0', this] at h3
      linarith
    exact ⟨hl2, by omega, by omega, this⟩

end Reach

section Main
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma A_props (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂)) :
    (∀ i j, 0 ≤ A₀ i j) ∧ (∀ i j, 0 ≤ A₁ i j) ∧ (∀ i j, 0 ≤ A₂ i j) ∧
      ∀ i, ∑ q, (A₀ i q + A₁ i q + A₂ i q) = 1 := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · simpa [qbdP] using hP.1 (1, i) (2, j)
  · simpa [qbdP] using hP.1 (1, i) (1, j)
  · simpa [qbdP] using hP.1 (1, i) (0, j)
  · have h := hP.2 (1, i)
    have h' : HasSum (qbdP B A₀ A₁ A₂ (1, i))
        (∑ x ∈ Finset.range 3 ×ˢ Finset.univ, qbdP B A₀ A₁ A₂ (1, i) x) :=
      hasSum_sum_of_ne_finset_zero (by
        rintro ⟨n, q⟩ hx
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true,
          not_lt] at hx
        simp only [qbdP]
        split_ifs <;> first | rfl | omega)
    rw [h.unique h', Finset.sum_product, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    simp only [qbdP, Finset.sum_add_distrib]
    norm_num
    ring

theorem main_real (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) : ∀ k,
    (1 ≤ k → IsUnit (1 - Ubar A₀ A₁ A₂ k)) ∧ (∀ i j, 0 ≤ Gbar A₀ A₁ A₂ k i j) ∧
      Gbar A₀ A₁ A₂ k *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
  obtain ⟨h0, h1, h2, hrow⟩ := A_props B A₀ A₁ A₂ hP
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨fun h => absurd h (by norm_num), fun i j => ?_, ?_⟩
    · show 0 ≤ (1 : Matrix ι ι ℝ) i j
      rw [Matrix.one_apply]; split_ifs <;> norm_num
    · show (1 : Matrix ι ι ℝ) *ᵥ _ = _
      rw [Matrix.one_mulVec]
  have hG : ∀ m, 1 ≤ m → m < k → (1 - Ubar A₀ A₁ A₂ m) * Gbar A₀ A₁ A₂ m = A₂ := by
    intro m hm1 hmk
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hu := (ih (m' + 1) hmk).1 hm1
    rw [Gbar_succ, ← mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), one_mul]
  have nonpos : ∀ a b : ι → ℝ, (∀ i, a i ≤ 0) → (1 - Ubar A₀ A₁ A₂ k) *ᵥ b = A₂ *ᵥ a →
      ∀ i, b i ≤ 0 := by
    intro a b ha hb
    refine maxP B A₀ A₁ A₂ hP.1 hirr h0 h1 h2 hrow k hk (Hs A₀ A₁ A₂ k a b) ha
      (Hs_top A₀ A₁ A₂ k hk a b) ?_ 1 le_rfl hk
    intro ℓ hl1 hlk i
    apply le_of_eq
    rcases Nat.lt_or_ge ℓ 2 with hl | hl
    · obtain rfl : ℓ = 1 := by omega
      exact congrFun (Hs_harm1 A₀ A₁ A₂ k hk a b hb) i
    · exact congrFun (Hs_harm A₀ A₁ A₂ k a b hG ℓ hl hlk) i
  have hU : IsUnit (1 - Ubar A₀ A₁ A₂ k) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv0
    funext i
    have e1 := nonpos 0 v (fun _ => le_rfl) (by rw [hv, Matrix.mulVec_zero])
    have e2 := nonpos 0 (-v) (fun _ => le_rfl)
      (by rw [Matrix.mulVec_neg, hv, neg_zero, Matrix.mulVec_zero])
    have a1 := e1 i
    have a2 := e2 i
    simp only [Pi.neg_apply, Pi.zero_apply] at a2 ⊢
    linarith
  have hGk : (1 - Ubar A₀ A₁ A₂ k) * Gbar A₀ A₁ A₂ k = A₂ := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Gbar_succ, ← mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), one_mul]
  refine ⟨fun _ => hU, fun i j => ?_, ?_⟩
  · have hcol : (fun i => Gbar A₀ A₁ A₂ k i j) = Gbar A₀ A₁ A₂ k *ᵥ Pi.single j 1 := by
      funext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have := nonpos (-(Pi.single j 1)) (-(fun i => Gbar A₀ A₁ A₂ k i j))
      (fun q => by simp only [Pi.neg_apply, Pi.single_apply]; split_ifs <;> norm_num)
      (by rw [hcol, Matrix.mulVec_neg, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hGk]) i
    simp only [Pi.neg_apply] at this
    linarith
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hprev := (ih k' (by omega)).2.2
    have e1 : (1 - Ubar A₀ A₁ A₂ (k' + 1)) *ᵥ (fun _ => (1:ℝ)) = A₂ *ᵥ (fun _ => 1) := by
      rw [Ubar_succ, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, hprev]
      funext i
      have := hrow i
      simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec, dotProduct, mul_one]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
      linarith
    have hinv := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
    rw [Gbar_succ, ← Matrix.mulVec_mulVec, ← e1, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

end Main


section PartC
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
noncomputable def phd {V : Type*} (T : Set V) (y0 : V) (F : V → ℝ≥0∞) (z : V) : ℝ≥0∞ :=
  if z ∈ T then (if z = y0 then 1 else 0) else F z

lemma fe_super {V : Type*} (P : V → V → ℝ) (T : Set V) (y0 : V) (hy0 : y0 ∈ T)
    (F : V → ℝ≥0∞)
    (hF : ∀ x, x ∉ T → ∑' z, ENNReal.ofReal (P x z) * phd T y0 F z ≤ F x) :
    ∀ x, ∑' t, g72mab_PS P x (t + 1) y0 (fun z => z ∉ T) ≤
      ∑' z, ENNReal.ofReal (P x z) * phd T y0 F z := by
  classical
  have key : ∀ n x, ∑ t ∈ Finset.range n, g72mab_PS P x (t + 1) y0 (fun z => z ∉ T) ≤
      ∑' z, ENNReal.ofReal (P x z) * phd T y0 F z := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Finset.sum_range_succ']
      have e : ∀ t, g72mab_PS P x (t + 1 + 1) y0 (fun z => z ∉ T) =
          ∑' z, ENNReal.ofReal (P x z) *
            (if z ∉ T then g72mab_PS P z (t + 1) y0 (fun z => z ∉ T) else 0) := by
        intro t
        rw [g72mab_PS_cons]
        refine tsum_congr fun z => ?_
        congr 1
        by_cases hz : z ∈ T <;> simp [hz]
      simp_rw [e]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), g72mab_PS_one]
      have hy : ENNReal.ofReal (P x y0) =
          ∑' z, ENNReal.ofReal (P x z) * (if z = y0 then 1 else 0) := by
        rw [tsum_eq_single y0]
        · simp
        · intro b hb; simp [hb]
      rw [hy, ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun z => ?_
      rw [← Finset.mul_sum, ← mul_add]
      gcongr
      by_cases hz : z ∈ T
      · simp [phd, hz]
      · have hzy : z ≠ y0 := fun h => hz (h ▸ hy0)
        simp only [phd, hz, not_false_eq_true, if_true, if_false, hzy, add_zero]
        exact (ih z).trans (hF z hz)
  intro x
  exact ENNReal.tsum_le_of_sum_range_le fun n => key n x

lemma qbd_expand (B A₀ A₁ A₂ : Matrix ι ι ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : ι)
    (φ : ℕ × ι → ℝ≥0∞) :
    ∑' z, ENNReal.ofReal (qbdP B A₀ A₁ A₂ (ℓ, i) z) * φ z =
      ∑ q, (ENNReal.ofReal (A₀ i q) * φ (ℓ + 1, q) + ENNReal.ofReal (A₁ i q) * φ (ℓ, q) +
        ENNReal.ofReal (A₂ i q) * φ (ℓ - 1, q)) := by
  have key : ∀ n q, ENNReal.ofReal (qbdP B A₀ A₁ A₂ (ℓ, i) (n, q)) * φ (n, q) =
      (if n = ℓ + 1 then ENNReal.ofReal (A₀ i q) * φ (ℓ + 1, q) else 0) +
      (if n = ℓ then ENNReal.ofReal (A₁ i q) * φ (ℓ, q) else 0) +
      (if n = ℓ - 1 then ENNReal.ofReal (A₂ i q) * φ (ℓ - 1, q) else 0) := by
    intro n q
    have hl0 : ℓ ≠ 0 := by omega
    simp only [qbdP, hl0, if_false]
    by_cases h1 : n = ℓ + 1
    · subst h1
      have a1 : ℓ + 1 ≠ ℓ := by omega
      have a2 : ℓ + 1 ≠ ℓ - 1 := by omega
      simp [a1, a2]
    by_cases h2 : n = ℓ
    · subst h2
      have a2 : n ≠ n - 1 := by omega
      have a3 : n + 1 ≠ n := by omega
      simp [a2, a3]
    by_cases h3 : n + 1 = ℓ
    · have a3 : n = ℓ - 1 := by omega
      subst a3
      simp [h1, h2, h3]
    · have a3 : n ≠ ℓ - 1 := by omega
      simp [h1, h2, h3, a3]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm, tsum_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [key]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq, tsum_ite_eq]

noncomputable def Fd (H : ℕ → ι → ℝ) (c k : ℕ) (z : ℕ × ι) : ℝ≥0∞ :=
  if c + 1 ≤ z.1 ∧ z.1 ≤ k then ENNReal.ofReal (H z.1 z.2) else ⊤

lemma phi_le (T : Set (ℕ × ι)) (c k : ℕ) (hck : c ≤ k)
    (hT : ∀ z : ℕ × ι, z ∈ T ↔ (z.1 ≤ c ∨ z.1 = k + 1))
    (j : ι) (H : ℕ → ι → ℝ) (Hc : ∀ q, H c q = if q = j then 1 else 0) :
    ∀ m q, c ≤ m → m ≤ k + 1 → phd T (c, j) (Fd H c k) (m, q) ≤ ENNReal.ofReal (H m q) := by
  classical
  intro m q h1 h2
  by_cases hm : m = c
  · subst hm
    have : ((m, q) : ℕ × ι) ∈ T := (hT _).mpr (Or.inl le_rfl)
    rw [phd, if_pos this, Hc]
    by_cases hq : q = j
    · simp [hq]
    · simp [hq]
  by_cases hk : m = k + 1
  · have : ((m, q) : ℕ × ι) ∈ T := (hT _).mpr (Or.inr hk)
    rw [phd, if_pos this, if_neg (by intro h; apply hm; exact congrArg Prod.fst h)]
    exact bot_le
  · have : ((m, q) : ℕ × ι) ∉ T := by rw [hT]; simp only; omega
    rw [phd, if_neg this, Fd, if_pos (by simp only; omega)]

lemma cmp_super (B A₀ A₁ A₂ : Matrix ι ι ℝ) (h0 : ∀ i j, 0 ≤ A₀ i j)
    (h1 : ∀ i j, 0 ≤ A₁ i j) (h2 : ∀ i j, 0 ≤ A₂ i j)
    (T : Set (ℕ × ι)) (c k : ℕ) (hck : c ≤ k)
    (hT : ∀ z : ℕ × ι, z ∈ T ↔ (z.1 ≤ c ∨ z.1 = k + 1))
    (j : ι) (H : ℕ → ι → ℝ) (Hc : ∀ q, H c q = if q = j then 1 else 0)
    (Hnn : ∀ ℓ q, 0 ≤ H ℓ q)
    (Hh : ∀ ℓ, c + 1 ≤ ℓ → ℓ ≤ k → H ℓ = A₀ *ᵥ H (ℓ + 1) + A₁ *ᵥ H ℓ + A₂ *ᵥ H (ℓ - 1)) :
    ∀ x, x ∉ T → ∑' z, ENNReal.ofReal (qbdP B A₀ A₁ A₂ x z) * phd T (c, j) (Fd H c k) z ≤
      Fd H c k x := by
  rintro ⟨ℓ, i⟩ hx
  rw [hT] at hx
  simp only at hx
  by_cases hlk : ℓ ≤ k
  swap
  · rw [Fd, if_neg (by simp only; omega)]; exact le_top
  rw [Fd, if_pos (by simp only; omega), qbd_expand B A₀ A₁ A₂ ℓ (by omega) i]
  simp only
  rw [congrFun (Hh ℓ (by omega) hlk) i]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => add_nonneg (add_nonneg
    (mul_nonneg (h0 _ _) (Hnn _ _)) (mul_nonneg (h1 _ _) (Hnn _ _))) (mul_nonneg (h2 _ _) (Hnn _ _)))]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (h0 _ _) (Hnn _ _)) (mul_nonneg (h1 _ _) (Hnn _ _)))
    (mul_nonneg (h2 _ _) (Hnn _ _)), ENNReal.ofReal_add (mul_nonneg (h0 _ _) (Hnn _ _))
    (mul_nonneg (h1 _ _) (Hnn _ _)), ENNReal.ofReal_mul (h0 _ _), ENNReal.ofReal_mul (h1 _ _),
    ENNReal.ofReal_mul (h2 _ _)]
  gcongr
  · exact phi_le T c k hck hT j H Hc (ℓ + 1) q (by omega) (by omega)
  · exact phi_le T c k hck hT j H Hc ℓ q (by omega) (by omega)
  · exact phi_le T c k hck hT j H Hc (ℓ - 1) q (by omega) (by omega)

lemma hG_all (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ m, 1 ≤ m → (1 - Ubar A₀ A₁ A₂ m) * Gbar A₀ A₁ A₂ m = A₂ := by
  intro m hm1
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hu := (main_real B A₀ A₁ A₂ hP hirr (m' + 1)).1 hm1
  rw [Gbar_succ, ← mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), one_mul]

lemma Gk_le (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (k : ℕ) (hk : 1 ≤ k) (i j : ι) :
    matGk (qbdP B A₀ A₁ A₂) k i j ≤ ENNReal.ofReal (Gbar A₀ A₁ A₂ k i j) := by
  classical
  obtain ⟨h0, h1, h2, -⟩ := A_props B A₀ A₁ A₂ hP
  have hGn : ∀ m i j, 0 ≤ Gbar A₀ A₁ A₂ m i j := fun m => (main_real B A₀ A₁ A₂ hP hirr m).2.1
  have hG := hG_all B A₀ A₁ A₂ hP hirr
  set e : ι → ℝ := fun q => if q = j then 1 else 0 with he
  have enn : ∀ q, 0 ≤ e q := fun q => by simp only [he]; split_ifs <;> norm_num
  have hb : ∀ q, 0 ≤ (Gbar A₀ A₁ A₂ k *ᵥ e) q := fun q =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hGn _ _ _) (enn l)
  set H := Hs A₀ A₁ A₂ k e (Gbar A₀ A₁ A₂ k *ᵥ e) with hH
  have Hnn := Hs_nonneg A₀ A₁ A₂ k e _ enn hb hGn
  set T : Set (ℕ × ι) := level 0 ∪ level (k + 1) with hTd
  have hT : ∀ z : ℕ × ι, z ∈ T ↔ (z.1 ≤ 0 ∨ z.1 = k + 1) := by
    intro z; simp [hTd, level]
  have Hh : ∀ ℓ, 0 + 1 ≤ ℓ → ℓ ≤ k → H ℓ = A₀ *ᵥ H (ℓ + 1) + A₁ *ᵥ H ℓ + A₂ *ᵥ H (ℓ - 1) := by
    intro ℓ hl1 hlk
    rcases Nat.lt_or_ge ℓ 2 with hl | hl
    · obtain rfl : ℓ = 1 := by omega
      exact Hs_harm1 A₀ A₁ A₂ k hk e _ (by rw [Matrix.mulVec_mulVec, hG k hk])
    · exact Hs_harm A₀ A₁ A₂ k e _ (fun m hm _ => hG m hm) ℓ hl hlk
  have hsup := cmp_super B A₀ A₁ A₂ h0 h1 h2 T 0 k (by omega) hT j H (fun q => rfl) Hnn Hh
  have hfe := fe_super (qbdP B A₀ A₁ A₂) T (0, j) (by simp [hT]) (Fd H 0 k) hsup (1, i)
  have hx : ((1, i) : ℕ × ι) ∉ T := by rw [hT]; simp only; omega
  calc matGk (qbdP B A₀ A₁ A₂) k i j =
      ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (1, i) (t + 1) (0, j) (fun z => z ∉ T) :=
        g72mab_fe _ _ _ _ ((hT _).mpr (by simp))
    _ ≤ _ := hfe
    _ ≤ Fd H 0 k (1, i) := hsup _ hx
    _ = _ := by
        rw [Fd, if_pos (by simp only; omega)]
        congr 1
        simp [hH, Hs, Matrix.mulVec, dotProduct, he]

lemma Uk_le (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (k : ℕ) (hk : 1 ≤ k) (i j : ι) :
    matUk (qbdP B A₀ A₁ A₂) k i j ≤ ENNReal.ofReal (Ubar A₀ A₁ A₂ k i j) := by
  classical
  obtain ⟨h0, h1, h2, -⟩ := A_props B A₀ A₁ A₂ hP
  have hGn : ∀ m i j, 0 ≤ Gbar A₀ A₁ A₂ m i j := fun m => (main_real B A₀ A₁ A₂ hP hirr m).2.1
  have hG := hG_all B A₀ A₁ A₂ hP hirr
  set e : ι → ℝ := fun q => if q = j then 1 else 0 with he
  have enn : ∀ q, 0 ≤ e q := fun q => by simp only [he]; split_ifs <;> norm_num
  set H := Hs A₀ A₁ A₂ k 0 e with hH
  have Hnn := Hs_nonneg A₀ A₁ A₂ k 0 e (fun _ => le_rfl) enn hGn
  set T : Set (ℕ × ι) := level 0 ∪ level 1 ∪ level (k + 1) with hTd
  have hT : ∀ z : ℕ × ι, z ∈ T ↔ (z.1 ≤ 1 ∨ z.1 = k + 1) := by
    intro z; simp only [hTd, level, Set.mem_union, Set.mem_ofPred_eq]; omega
  have Hh : ∀ ℓ, 1 + 1 ≤ ℓ → ℓ ≤ k → H ℓ = A₀ *ᵥ H (ℓ + 1) + A₁ *ᵥ H ℓ + A₂ *ᵥ H (ℓ - 1) :=
    fun ℓ hl hlk => Hs_harm A₀ A₁ A₂ k 0 e (fun m hm _ => hG m hm) ℓ hl hlk
  have hsup := cmp_super B A₀ A₁ A₂ h0 h1 h2 T 1 k hk hT j H (fun q => rfl) Hnn Hh
  have hfe := fe_super (qbdP B A₀ A₁ A₂) T (1, j) (by simp [hT]) (Fd H 1 k) hsup (1, i)
  have hreal : ∑ q, (A₀ i q * H 2 q + A₁ i q * H 1 q) = Ubar A₀ A₁ A₂ k i j := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have e2 : H 2 = Gbar A₀ A₁ A₂ k' *ᵥ e := by
      rw [hH, show (2 : ℕ) = 0 + 2 from rfl, Hs_two_add]
      congr 2
    rw [e2, Ubar_succ]
    simp [hH, Hs, Matrix.mulVec, dotProduct, he, Matrix.mul_apply, Finset.sum_add_distrib,
      add_comm]
  calc matUk (qbdP B A₀ A₁ A₂) k i j =
      ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (1, i) (t + 1) (1, j) (fun z => z ∉ T) :=
        g72mab_fe _ _ _ _ ((hT _).mpr (by simp))
    _ ≤ _ := hfe
    _ = _ := qbd_expand B A₀ A₁ A₂ 1 le_rfl i _
    _ ≤ ∑ q, (ENNReal.ofReal (A₀ i q) * ENNReal.ofReal (H 2 q) +
          ENNReal.ofReal (A₁ i q) * ENNReal.ofReal (H 1 q) + ENNReal.ofReal (A₂ i q) * 0) := by
        gcongr with q
        · exact phi_le T 1 k hk hT j H (fun q => rfl) 2 q (by omega) (by omega)
        · exact phi_le T 1 k hk hT j H (fun q => rfl) 1 q le_rfl (by omega)
        · have hm : ((1 - 1, q) : ℕ × ι) ∈ T := by rw [hT]; simp
          rw [phd, if_pos hm, if_neg (by simp)]
    _ = _ := by
        rw [← hreal, ENNReal.ofReal_sum_of_nonneg (fun q _ => add_nonneg
          (mul_nonneg (h0 _ _) (Hnn _ _)) (mul_nonneg (h1 _ _) (Hnn _ _)))]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_zero, add_zero, ENNReal.ofReal_add (mul_nonneg (h0 _ _) (Hnn _ _))
          (mul_nonneg (h1 _ _) (Hnn _ _)), ENNReal.ofReal_mul (h0 _ _), ENNReal.ofReal_mul (h1 _ _)]

lemma Gk_le_G (P : ℕ × ι → ℕ × ι → ℝ) (k : ℕ) (i j : ι) : matGk P k i j ≤ matG P i j := by
  classical
  rw [show matGk P k i j = ∑' t, g72mab_PS P (1, i) (t + 1) (0, j)
      (fun z => z ∉ level 0 ∪ level (k + 1)) from g72mab_fe _ _ _ _ (Or.inl rfl),
    show matG P i j = ∑' t, g72mab_PS P (1, i) (t + 1) (0, j) (fun z => z ∉ level 0) from
      g72mab_fe _ _ _ _ rfl]
  exact ENNReal.tsum_le_tsum fun t => g72mab_PS_mono P _ _ (fun z hz h => hz (Or.inl h)) _ _ _

lemma PS_len (B A₀ A₁ A₂ : Matrix ι ι ℝ) (k : ℕ) (y : ℕ × ι) :
    ∀ L x, x.1 + L ≤ k + 1 → g72mab_PS (qbdP B A₀ A₁ A₂) x L y (fun z => z ∉ level 0) =
      g72mab_PS (qbdP B A₀ A₁ A₂) x L y (fun z => z ∉ level 0 ∪ level (k + 1)) := by
  classical
  intro L
  induction L with
  | zero => intro x _; rw [g72mab_PS_zero, g72mab_PS_zero]
  | succ L ih =>
    intro x hx
    rw [g72mab_PS_cons _ x L y (fun z => z ∉ level 0),
      g72mab_PS_cons _ x L y (fun z => z ∉ level 0 ∪ level (k + 1))]
    refine tsum_congr fun z => ?_
    by_cases hP0 : qbdP B A₀ A₁ A₂ x z = 0
    · simp [hP0]
    have hz := (g72mab_qnz B A₀ A₁ A₂ x z hP0).1
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp only [true_or, if_true, g72mab_PS_zero]
    · have hiff : (z ∉ level 0) ↔ (z ∉ level 0 ∪ level (k + 1)) := by
        simp only [level, Set.mem_union, Set.mem_ofPred_eq]; omega
      by_cases hA : z ∉ level 0
      · rw [if_pos (Or.inr hA), if_pos (Or.inr (hiff.mp hA)), ih z (by omega)]
      · rw [if_neg (by rintro (h | h) <;> [omega; exact hA h]),
          if_neg (by rintro (h | h) <;> [omega; exact hA (hiff.mpr h)])]

lemma Gk_tendsto (B A₀ A₁ A₂ : Matrix ι ι ℝ) (i j : ι) :
    Filter.Tendsto (fun k => matGk (qbdP B A₀ A₁ A₂) k i j) Filter.atTop
      (nhds (matG (qbdP B A₀ A₁ A₂) i j)) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  set a : ℕ → ℝ≥0∞ := fun t => g72mab_PS P (1, i) (t + 1) (0, j) (fun z => z ∉ level 0) with ha
  have hG : matG P i j = ∑' t, a t := g72mab_fe _ _ _ _ rfl
  have hlow : ∀ k, ∑ t ∈ Finset.range k, a t ≤ matGk P k i j := by
    intro k
    rw [show matGk P k i j = ∑' t, g72mab_PS P (1, i) (t + 1) (0, j)
        (fun z => z ∉ level 0 ∪ level (k + 1)) from g72mab_fe _ _ _ _ (Or.inl rfl)]
    calc ∑ t ∈ Finset.range k, a t = ∑ t ∈ Finset.range k, g72mab_PS P (1, i) (t + 1) (0, j)
          (fun z => z ∉ level 0 ∪ level (k + 1)) :=
          Finset.sum_congr rfl fun t ht =>
            PS_len B A₀ A₁ A₂ k (0, j) (t + 1) (1, i) (by
              have := Finset.mem_range.mp ht; simp only; omega)
      _ ≤ _ := ENNReal.sum_le_tsum _
  have h1 : Filter.Tendsto (fun k => ∑ t ∈ Finset.range k, a t) Filter.atTop
      (nhds (matG P i j)) := by
    rw [hG]; exact ENNReal.tendsto_nat_tsum a
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow
    (fun k => Gk_le_G P k i j)

lemma G_fin (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x) (i : ι) :
    ∑ j, matG (qbdP B A₀ A₁ A₂) i j = 1 ∧ ∀ j, matG (qbdP B A₀ A₁ A₂) i j ≠ ⊤ := by
  have hsum : ∑ j, matG (qbdP B A₀ A₁ A₂) i j = 1 := by
    have := g72mab_G_sum B A₀ A₁ A₂ hP hirr hrec i
    rwa [tsum_fintype] at this
  refine ⟨hsum, fun j => ne_top_of_le_ne_top ENNReal.one_ne_top ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (f := fun j => matG (qbdP B A₀ A₁ A₂) i j)
    (fun _ _ => bot_le) (Finset.mem_univ j)

lemma Gbar_tendsto (B A₀ A₁ A₂ : Matrix ι ι ℝ) (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x) (i j : ι) :
    Filter.Tendsto (fun k => Gbar A₀ A₁ A₂ k i j) Filter.atTop
      (nhds ((matG (qbdP B A₀ A₁ A₂) i j).toReal)) := by
  set P := qbdP B A₀ A₁ A₂ with hPd
  obtain ⟨hsum, hfin⟩ := G_fin B A₀ A₁ A₂ hP hirr hrec i
  set g : ℕ → ι → ℝ := fun k j => (matGk P k i j).toReal with hgd
  have hg : ∀ j, Filter.Tendsto (fun k => g k j) Filter.atTop (nhds ((matG P i j).toReal)) :=
    fun j => (ENNReal.tendsto_toReal (hfin j)).comp (Gk_tendsto B A₀ A₁ A₂ i j)
  have hs1 : ∑ j, (matG P i j).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun j _ => hfin j), hsum, ENNReal.toReal_one]
  have hgs : Filter.Tendsto (fun k => ∑ j, g k j) Filter.atTop (nhds 1) :=
    hs1 ▸ tendsto_finsetSum _ fun j _ => hg j
  have hle : ∀ k, 1 ≤ k → ∀ j, g k j ≤ Gbar A₀ A₁ A₂ k i j := fun k hk j =>
    ENNReal.toReal_le_of_le_ofReal ((main_real B A₀ A₁ A₂ hP hirr k).2.1 i j)
      (Gk_le B A₀ A₁ A₂ hP hirr k hk i j)
  have hrow : ∀ k, ∑ j, Gbar A₀ A₁ A₂ k i j = 1 := fun k => by
    have := congrFun (main_real B A₀ A₁ A₂ hP hirr k).2.2 i
    simpa [Matrix.mulVec, dotProduct] using this
  have hup : ∀ k, 1 ≤ k → Gbar A₀ A₁ A₂ k i j ≤ g k j + (1 - ∑ j, g k j) := by
    intro k hk
    have := Finset.single_le_sum (f := fun j' => Gbar A₀ A₁ A₂ k i j' - g k j')
      (fun j' _ => sub_nonneg.mpr (hle k hk j')) (Finset.mem_univ j)
    simp only [Finset.sum_sub_distrib, hrow] at this
    linarith
  have hlim2 : Filter.Tendsto (fun k => g k j + (1 - ∑ j, g k j)) Filter.atTop
      (nhds ((matG P i j).toReal + (1 - 1))) := (hg j).add (tendsto_const_nhds.sub hgs)
  rw [sub_self, add_zero] at hlim2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg j) hlim2
    (Filter.eventually_atTop.2 ⟨1, fun k hk => hle k hk j⟩) (Filter.eventually_atTop.2 ⟨1, hup⟩)

lemma U_eq (B A₀ A₁ A₂ : Matrix ι ι ℝ) (i j : ι) :
    matU (qbdP B A₀ A₁ A₂) i j = ENNReal.ofReal (A₁ i j) +
      ∑ q, ENNReal.ofReal (A₀ i q) * matG (qbdP B A₀ A₁ A₂) q j := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hA : (fun z : ℕ × ι => z ∉ level 0 ∪ level 1) = fun z => 0 + 1 < z.1 := by
    funext z; simp only [level, Set.mem_union, Set.mem_ofPred_eq, eq_iff_iff]; omega
  have hA0 : (fun z : ℕ × ι => z ∉ level 0) = fun z => 0 < z.1 := by
    funext z; simp only [level, Set.mem_ofPred_eq, eq_iff_iff]; omega
  have hU : matU P i j = ∑' t, g72mab_PS P (1, i) (t + 1) (1, j) (fun z => 0 + 1 < z.1) := by
    rw [← hA]; exact g72mab_fe _ _ _ _ (Or.inr rfl)
  have hGq : ∀ q, matG P q j = ∑' t, g72mab_PS P (1, q) (t + 1) (0, j) (fun z => 0 < z.1) := by
    intro q; rw [← hA0]; exact g72mab_fe _ _ _ _ rfl
  rw [hU, tsum_eq_zero_add' ENNReal.summable, g72mab_PS_one]
  congr 1
  · have e : ∀ t, g72mab_PS P (1, i) (t + 1 + 1) (1, j) (fun z => 0 + 1 < z.1) =
        ∑ q, ENNReal.ofReal (A₀ i q) * g72mab_PS P (1, q) (t + 1) (0, j) (fun z => 0 < z.1) := by
      intro t
      rw [g72mab_PS_cons, qbd_expand B A₀ A₁ A₂ 1 le_rfl i]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [if_pos (Or.inr (by simp)), if_neg (by simp), if_neg (by simp), mul_zero, mul_zero,
        add_zero, add_zero]
      exact congrArg _ (g72mab_PS_shiftN B A₀ A₁ A₂ 0 1 0 q j le_rfl (t + 1))
    simp_rw [e, hGq]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    simp_rw [ENNReal.tsum_mul_left]

end PartC

end S202IA

open MatrixAnalytic.MinimalSolutions in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : Matrix ι ι ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hrec : ∀ x : ℕ × ι, Recurrent (qbdP B A₀ A₁ A₂) x) :
    (∀ k : ℕ, 1 ≤ k → IsUnit (1 - Ubar A₀ A₁ A₂ k)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (∀ i j, 0 ≤ Ubar A₀ A₁ A₂ k i j) ∧ ∀ i, ∑ j, Ubar A₀ A₁ A₂ k i j ≤ 1) ∧
      (∀ k : ℕ, (∀ i j, 0 ≤ Gbar A₀ A₁ A₂ k i j) ∧ ∀ i, ∑ j, Gbar A₀ A₁ A₂ k i j = 1) ∧
      (∀ i j, Filter.Tendsto (fun k => ENNReal.ofReal (Ubar A₀ A₁ A₂ k i j)) Filter.atTop
        (nhds (matU (qbdP B A₀ A₁ A₂) i j))) ∧
      (∀ i j, Filter.Tendsto (fun k => ENNReal.ofReal (Gbar A₀ A₁ A₂ k i j)) Filter.atTop
        (nhds (matG (qbdP B A₀ A₁ A₂) i j))) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ i j,
        matGk (qbdP B A₀ A₁ A₂) k i j ≤ ENNReal.ofReal (Gbar A₀ A₁ A₂ k i j) ∧
          matUk (qbdP B A₀ A₁ A₂) k i j ≤ ENNReal.ofReal (Ubar A₀ A₁ A₂ k i j)) := by
  have hR := S202IA.main_real B A₀ A₁ A₂ hP hirr
  obtain ⟨h0, h1, h2, hrowA⟩ := S202IA.A_props B A₀ A₁ A₂ hP
  have hGrow : ∀ k i, ∑ j, Gbar A₀ A₁ A₂ k i j = 1 := fun k i => by
    have := congrFun (hR k).2.2 i
    simpa [Matrix.mulVec, dotProduct] using this
  have hUb : ∀ k i j, Ubar A₀ A₁ A₂ k i j = A₁ i j + ∑ q, A₀ i q * Gbar A₀ A₁ A₂ (k - 1) q j :=
    fun k i j => by simp [Ubar, Matrix.mul_apply]
  refine ⟨fun k hk => (hR k).1 hk, fun k hk => ⟨fun i j => ?_, fun i => ?_⟩,
    fun k => ⟨(hR k).2.1, hGrow k⟩, fun i j => ?_, fun i j => ?_,
    fun k hk i j => ⟨S202IA.Gk_le B A₀ A₁ A₂ hP hirr k hk i j,
      S202IA.Uk_le B A₀ A₁ A₂ hP hirr k hk i j⟩⟩
  · rw [hUb]
    exact add_nonneg (h1 i j) (Finset.sum_nonneg fun q _ => mul_nonneg (h0 i q) ((hR _).2.1 q j))
  · simp only [hUb, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hGrow, mul_one]
    have := hrowA i
    simp only [Finset.sum_add_distrib] at this
    have : 0 ≤ ∑ q, A₂ i q := Finset.sum_nonneg fun q _ => h2 i q
    linarith
  · rw [S202IA.U_eq]
    have hreal : Filter.Tendsto (fun k => Ubar A₀ A₁ A₂ k i j) Filter.atTop
        (nhds (A₁ i j + ∑ q, A₀ i q * (matG (qbdP B A₀ A₁ A₂) q j).toReal)) := by
      simp only [hUb]
      exact tendsto_const_nhds.add (tendsto_finsetSum _ fun q _ => tendsto_const_nhds.mul
        ((S202IA.Gbar_tendsto B A₀ A₁ A₂ hP hirr hrec q j).comp (Filter.tendsto_sub_atTop_nat 1)))
    have := ENNReal.tendsto_ofReal hreal
    convert this using 2
    rw [ENNReal.ofReal_add (h1 i j) (Finset.sum_nonneg fun q _ => mul_nonneg (h0 i q)
      ENNReal.toReal_nonneg), ENNReal.ofReal_sum_of_nonneg fun q _ => mul_nonneg (h0 i q)
      ENNReal.toReal_nonneg]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ENNReal.ofReal_mul (h0 i q), ENNReal.ofReal_toReal ((S202IA.G_fin B A₀ A₁ A₂ hP hirr hrec q).2 j)]
  · have := ENNReal.tendsto_ofReal (S202IA.Gbar_tendsto B A₀ A₁ A₂ hP hirr hrec i j)
    rwa [ENNReal.ofReal_toReal ((S202IA.G_fin B A₀ A₁ A₂ hP hirr hrec i).2 j)] at this
