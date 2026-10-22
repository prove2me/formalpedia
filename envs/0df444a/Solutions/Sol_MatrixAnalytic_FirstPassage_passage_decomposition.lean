-- Prove2me | solution 1 for MatrixAnalytic.FirstPassage.passage_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T18:16:23.314015+00:00
-- url     : https://prove2.me/submissions/c139a870-de46-4b73-9625-17050828fd26

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage

open scoped ENNReal
open Matrix
open MatrixAnalytic.FirstPassage

noncomputable def g72ma_W {V : Type*} (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ s : Fin t, ENNReal.ofReal (P (ω s.castSucc) (ω s.succ))

open Classical in
noncomputable def g72ma_PS {V : Type*} (P : V → V → ℝ) (x : V) (L : ℕ) (y : V) (A : V → Prop) :
    ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → V,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then g72ma_W P ω else 0

section Gen
variable {V : Type*} (P : V → V → ℝ)

lemma g72ma_W_cons {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72ma_W P (Fin.cons k ω : Fin (n + 2) → V) = ENNReal.ofReal (P k (ω 0)) * g72ma_W P ω := by
  unfold g72ma_W
  rw [Fin.prod_univ_succ]
  congr 1

lemma g72ma_W_snoc {n : ℕ} (ω : Fin (n + 1) → V) (k : V) :
    g72ma_W P (Fin.snoc ω k : Fin (n + 2) → V) = g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last n)) k) := by
  unfold g72ma_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g72ma_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' ω : Fin (n + 1) → V, ∑' k : V, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g72ma_tsum_cons {n : ℕ} (f : (Fin (n + 2) → V) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → V, f ω = ∑' k : V, ∑' ω : Fin (n + 1) → V, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => V)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g72ma_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

open Classical in
lemma g72ma_PS_zero (x y : V) (A : V → Prop) :
    g72ma_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g72ma_PS
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [g72ma_W]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g72ma_cond_cons {L : ℕ} (x y : V) (A : V → Prop) (ω : Fin (L + 1) → V) :
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

lemma g72ma_PS_cons (x : V) (L : ℕ) (y : V) (A : V → Prop) [DecidablePred A] :
    g72ma_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g72ma_PS P z L y A else 0) := by
  classical
  unfold g72ma_PS
  rw [g72ma_tsum_cons, tsum_eq_single x]
  · simp_rw [g72ma_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g72ma_cond_cons x y A ω
      rw [g72ma_W_cons]
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

lemma g72ma_PS_one (x y : V) (A : V → Prop) :
    g72ma_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g72ma_PS_cons P, tsum_eq_single y]
  · simp [g72ma_PS_zero]
  · intro z hz; simp [g72ma_PS_zero, hz]

open Classical in
noncomputable def g72ma_AV (x : V) (A : V → Prop) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then g72ma_W P ω else 0

open Classical in
noncomputable def g72ma_EX (x : V) (A : V → Prop) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → V,
    if ω 0 = x ∧ ¬ A (ω (Fin.last k)) ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → A (ω m))
    then g72ma_W P ω else 0

lemma g72ma_step (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72ma_AV P x A (t + 1) + g72ma_EX P x A (t + 1) = g72ma_AV P x A t := by
  classical
  unfold g72ma_AV g72ma_EX
  rw [g72ma_tsum_snoc, g72ma_tsum_snoc, ← ENNReal.tsum_add]
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
  simp_rw [hz, hA, hB, Fin.snoc_last, g72ma_W_snoc]
  by_cases hc : ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) ∧ A k then
        g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) +
        if ω 0 = x ∧ ¬ A k ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i) then
        g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) else 0) =
        g72ma_W P ω * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
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

lemma g72ma_mass (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x : V) (A : V → Prop) (t : ℕ) :
    g72ma_AV P x A t + ∑ k ∈ Finset.range t, g72ma_EX P x A (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g72ma_AV
    rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [g72ma_W]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g72ma_EX P x A (t + 1)), ← add_assoc,
      add_comm (g72ma_EX P x A (t + 1)), g72ma_step P hrow x A t, ih]

lemma g72ma_PS_le_EX (x y : V) (A : V → Prop) (hy : ¬ A y) (k : ℕ) :
    g72ma_PS P x k y A ≤ g72ma_EX P x A k := by
  classical
  unfold g72ma_PS g72ma_EX
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.1 ▸ hy, h1.2.2⟩ h2
  · simp
  · exact le_rfl

lemma g72ma_sum_PS_le (hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1) (x y : V) (A : V → Prop)
    (hy : ¬ A y) : ∑' k, g72ma_PS P x (k + 1) y A ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← g72ma_mass P hrow x A t]
  exact (Finset.sum_le_sum fun k _ => g72ma_PS_le_EX P x y A hy (k + 1)).trans le_add_self

/-- first-passage convolution for a skip-free-down chain with level function `lev`. -/
lemma g72ma_conv (lev : V → ℕ) (hskip : ∀ x z, lev z + 1 < lev x → P x z = 0) (m : ℕ) (y : V)
    (hy : lev y = m) :
    ∀ L x, m + 2 ≤ lev x → g72ma_PS P x (L + 1) y (fun z => m < lev z) =
      ∑ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72ma_PS P x (s + 1) z (fun z => m + 1 < lev z) * g72ma_PS P z (L - s) y (fun z => m < lev z)
        else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [g72ma_PS_one, hskip x y (by omega)]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72ma_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if lev z = m + 1 then g72ma_PS P x (0 + 1) z (fun z => m + 1 < lev z) *
        g72ma_PS P z (L + 1 - 0) y (fun z => m < lev z) else 0) =
        if lev z = m + 1 then ENNReal.ofReal (P x z) * g72ma_PS P z (L + 1) y (fun z => m < lev z)
        else 0 := fun z => by
      rw [g72ma_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if lev z = m + 1 then
        g72ma_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
        g72ma_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then ∑' z, (if lev z = m + 1 then
          g72ma_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72ma_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if lev z = m + 1 then
          g72ma_PS P x (s + 1 + 1) z (fun z => m + 1 < lev z) *
          g72ma_PS P z (L + 1 - (s + 1)) y (fun z => m < lev z) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if m + 1 < lev w then (if lev z = m + 1 then
          g72ma_PS P w (s + 1) z (fun z => m + 1 < lev z) *
          g72ma_PS P z (L - s) y (fun z => m < lev z) else 0) else 0) := by
        intro z
        rw [g72ma_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
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

section Gen2
variable {V : Type*} (P : V → V → ℝ)

lemma g72ma_conv2 (Inv mid A A' : V → Prop) [DecidablePred mid]
    (hstep : ∀ x w, Inv x → P x w ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ Inv w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w))
    (y : V) (hy : ∀ x, Inv x → P x y = 0) :
    ∀ L x, Inv x → g72ma_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range L, ∑' z, (if mid z then
        g72ma_PS P x (s + 1) z A' * g72ma_PS P z (L - s) y A else 0) := by
  classical
  intro L
  induction L with
  | zero =>
    intro x hx
    rw [g72ma_PS_one, hy x hx]
    simp
  | succ L ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72ma_PS_cons P x (L + 1)]
    have h0 : ∀ z, (if mid z then g72ma_PS P x (0 + 1) z A' *
        g72ma_PS P z (L + 1 - 0) y A else 0) =
        if mid z then ENNReal.ofReal (P x z) * g72ma_PS P z (L + 1) y A
        else 0 := fun z => by
      rw [g72ma_PS_one, Nat.sub_zero]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range L, ∑' z, (if mid z then
        g72ma_PS P x (s + 1 + 1) z A' *
        g72ma_PS P z (L + 1 - (s + 1)) y A else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if A' w then ∑' z, (if mid z then
          g72ma_PS P w (s + 1) z A' *
          g72ma_PS P z (L - s) y A else 0) else 0) := by
      intro s _
      have e : ∀ z, (if mid z then
          g72ma_PS P x (s + 1 + 1) z A' *
          g72ma_PS P z (L + 1 - (s + 1)) y A else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if A' w then (if mid z then
          g72ma_PS P w (s + 1) z A' *
          g72ma_PS P z (L - s) y A else 0) else 0) := by
        intro z
        rw [g72ma_PS_cons P x (s + 1), show L + 1 - (s + 1) = L - s by omega]
        by_cases hz : mid z
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun w => ?_
          by_cases hw : A' w
          · simp [hw, mul_assoc]
          · simp [hw]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hw : A' w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hPw : P x w = 0
    · simp [hPw]
    rcases hstep x w hx hPw with ⟨hm, hA, hA'⟩ | ⟨hA', hA, hI, hm⟩ | ⟨hA, hA', hm⟩
    · simp [hm, hA, hA']
    · rw [if_pos (Or.inr hA), ih w hI]
      simp [hm, hA']
    · simp [hA, hA', hm]

lemma g72ma_AV_cons (x : V) (A : V → Prop) (t : ℕ) [DecidablePred A] :
    g72ma_AV P x A (t + 1) =
      ∑' z, ENNReal.ofReal (P x z) * (if A z then g72ma_AV P z A t else 0) := by
  classical
  unfold g72ma_AV
  rw [g72ma_tsum_cons, tsum_eq_single x]
  · simp_rw [g72ma_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc : ((Fin.cons x ω : Fin (t + 2) → V) 0 = x ∧ ∀ i : Fin (t + 2), i ≠ 0 →
          A ((Fin.cons x ω : Fin (t + 2) → V) i)) ↔
          (A (ω 0) ∧ ∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) := by
        rw [Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, ne_eq, not_true_eq_false, IsEmpty.forall_iff,
          true_and, Fin.succ_ne_zero, not_false_eq_true, forall_const]
        constructor
        · intro h; exact ⟨h 0, fun i _ => h i⟩
        · rintro ⟨h0, h⟩ i
          by_cases hi : i = 0
          · subst hi; exact h0
          · exact h i hi
      simp only [hcc, g72ma_W_cons]
      by_cases h1 : A (ω 0) <;> by_cases h2 : (∀ i : Fin (t + 1), i ≠ 0 → A (ω i)) <;> simp [h1, h2]
    · intro z hz
      simp [Ne.symm hz]
  · intro k hk
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma g72ma_AV_zero (x : V) (A : V → Prop) : g72ma_AV P x A 0 = 1 := by
  classical
  unfold g72ma_AV
  rw [← (Equiv.funUnique (Fin 1) V).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  rw [tsum_eq_single x]
  · simp [g72ma_W]
  · intro b hb; simp [hb]

lemma g72ma_decAV (Inv mid A A' : V → Prop) [DecidablePred mid]
    (hstep : ∀ x w, Inv x → P x w ≠ 0 →
      (mid w ∧ A w ∧ ¬ A' w) ∨ (A' w ∧ A w ∧ Inv w ∧ ¬ mid w) ∨ (¬ A w ∧ ¬ A' w ∧ ¬ mid w)) :
    ∀ t x, Inv x → g72ma_AV P x A t = g72ma_AV P x A' t +
      ∑ s ∈ Finset.range t, ∑' z, (if mid z then
        g72ma_PS P x (s + 1) z A' * g72ma_AV P z A (t - (s + 1)) else 0) := by
  classical
  intro t
  induction t with
  | zero => intro x _; simp [g72ma_AV_zero]
  | succ t ih =>
    intro x hx
    rw [Finset.sum_range_succ', g72ma_AV_cons P x A t, g72ma_AV_cons P x A' t]
    have h0 : ∀ z, (if mid z then g72ma_PS P x (0 + 1) z A' *
        g72ma_AV P z A (t + 1 - (0 + 1)) else 0) =
        if mid z then ENNReal.ofReal (P x z) * g72ma_AV P z A t else 0 := fun z => by
      rw [g72ma_PS_one, show t + 1 - (0 + 1) = t by omega]
    simp_rw [h0]
    have h1 : ∀ s ∈ Finset.range t, ∑' z, (if mid z then
        g72ma_PS P x (s + 1 + 1) z A' * g72ma_AV P z A (t + 1 - (s + 1 + 1)) else 0) =
        ∑' w, ENNReal.ofReal (P x w) * (if A' w then ∑' z, (if mid z then
          g72ma_PS P w (s + 1) z A' * g72ma_AV P z A (t - (s + 1)) else 0) else 0) := by
      intro s _
      have e : ∀ z, (if mid z then
          g72ma_PS P x (s + 1 + 1) z A' * g72ma_AV P z A (t + 1 - (s + 1 + 1)) else 0) =
          ∑' w, ENNReal.ofReal (P x w) * (if A' w then (if mid z then
          g72ma_PS P w (s + 1) z A' * g72ma_AV P z A (t - (s + 1)) else 0) else 0) := by
        intro z
        rw [g72ma_PS_cons P x (s + 1), show t + 1 - (s + 1 + 1) = t - (s + 1) by omega]
        by_cases hz : mid z
        · simp only [hz, if_true]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun w => ?_
          by_cases hw : A' w
          · simp [hw, mul_assoc]
          · simp [hw]
        · simp [hz]
      simp_rw [e]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun w => ?_
      rw [ENNReal.tsum_mul_left]
      by_cases hw : A' w
      · simp only [hw, if_true]
      · simp [hw]
    rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun w => ?_
    rw [← Finset.mul_sum]
    by_cases hPw : P x w = 0
    · simp [hPw]
    rcases hstep x w hx hPw with ⟨hm, hA, hA'⟩ | ⟨hA', hA, hI, hm⟩ | ⟨hA, hA', hm⟩
    · simp [hm, hA, hA']
    · rw [if_pos hA, ih w hI]
      simp [hm, hA', mul_add]
    · simp [hA, hA', hm]

end Gen2
lemma g72ma_cauchy (a b : ℕ → ℝ≥0∞) :
    ∑' k, ∑ s ∈ Finset.range k, a (s + 1) * b (k - s) = (∑' s, a (s + 1)) * ∑' t, b (t + 1) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Finset.range_zero, Finset.sum_empty, zero_add]
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun s t => a (s + 1) * b (t + 1)),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun k => ?_
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal k)
    (fun p : ℕ × ℕ => a (p.1 + 1) * b (p.2 + 1)), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun s t => a (s + 1) * b (t + 1))]
  refine Finset.sum_congr rfl fun s hs => ?_
  have : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [show k + 1 - s = k - s + 1 by omega]


lemma g72ma_hd {V : Type*} (P : V → V → ℝ) (K : Set V) (x y : V) (hy : y ∈ K) :
    hitDist P K x y = ∑' t, g72ma_PS P x (t + 1) y (fun w => w ∉ K) := by
  classical
  unfold hitDist g72ma_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ K ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ K) ↔
      (ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ K) := by
    simp only [hy, true_and]
  by_cases h : ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧
      ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ K
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

lemma g72ma_at {V : Type*} (P : V → V → ℝ) (K : Set V) (x : V) (t : ℕ) :
    avoidTail P K x t = g72ma_AV P x (fun w => w ∉ K) t := by
  classical
  unfold avoidTail g72ma_AV
  refine tsum_congr fun ω => ?_
  by_cases h : ω 0 = x ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ K
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]


lemma g72ma_levn {ι : Type*} (n : ℕ) (f : ℕ × ι → ℝ≥0∞) :
    ∑' z : ℕ × ι, (if z.1 = n then f z else 0) = ∑' l, f (n, l) := by
  rw [ENNReal.tsum_prod', tsum_eq_single n]
  · simp
  · intro m hm; simp [hm]

lemma g72ma_swap {V : Type*} (mid : V → Prop) [DecidablePred mid] (a : V → ℕ → ℝ≥0∞)
    (b : V → ℕ → ℝ≥0∞) :
    ∑' t, ∑ s ∈ Finset.range t, ∑' z, (if mid z then a z (s + 1) * b z (t - s) else 0) =
      ∑' z, if mid z then (∑' s, a z (s + 1)) * ∑' u, b z (u + 1) else 0 := by
  simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  by_cases hz : mid z
  · simp only [hz, if_true]
    exact g72ma_cauchy (a z) (b z)
  · simp [hz]

lemma g72ma_fup {ι : Type*} (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ) (x w : ℕ × ι)
    (h : finiteQBD M P₀₀ A₀ A₁ A₂ P_MM x w ≠ 0) : w.1 ≤ x.1 + 1 := by
  unfold finiteQBD at h
  split_ifs at h <;> first | omega | exact absurd rfl h

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n k : ℕ) (hnk : n < k) (hkM : k ≤ M) :
    tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n k =
        tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) +
          GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) *ᵥ
            tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + 1) k ∧
      GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n k =
        GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) *
          GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + 1) k := by
  classical
  set Q := finiteQBD M P₀₀ A₀ A₁ A₂ P_MM with hQd
  rcases Nat.lt_or_ge (n + 1) k with hk | hk
  swap
  · have hk' : k = n + 1 := by omega
    subst hk'
    refine ⟨?_, ?_⟩
    · have : tPass Q (n + 1) (n + 1) = 0 := by funext i; simp [tPass]
      rw [this, Matrix.mulVec_zero, add_zero]
    · have : GammaPass Q (n + 1) (n + 1) = 1 := by
        funext i j; simp [GammaPass, Matrix.one_apply]
      rw [this, Matrix.mul_one]
  have hstep : ∀ x w, (fun x : ℕ × ι => x.1 ≤ n) x → Q x w ≠ 0 →
      ((fun z : ℕ × ι => z.1 = n + 1) w ∧ (fun w => w ∉ (level k : Set (ℕ × ι))) w ∧
        ¬ (fun w => w ∉ (level (n + 1) : Set (ℕ × ι))) w) ∨
      ((fun w => w ∉ (level (n + 1) : Set (ℕ × ι))) w ∧ (fun w => w ∉ (level k : Set (ℕ × ι))) w ∧
        (fun x : ℕ × ι => x.1 ≤ n) w ∧ ¬ (fun z : ℕ × ι => z.1 = n + 1) w) ∨
      (¬ (fun w => w ∉ (level k : Set (ℕ × ι))) w ∧ ¬ (fun w => w ∉ (level (n + 1) : Set (ℕ × ι))) w ∧
        ¬ (fun z : ℕ × ι => z.1 = n + 1) w) := by
    intro x w hx hw
    have := g72ma_fup M P₀₀ A₀ A₁ A₂ P_MM x w hw
    simp only [level, Set.mem_setOf_eq]
    rcases Nat.lt_or_ge w.1 (n + 1) with h | h
    · right; left; omega
    · left; omega
  have hnk' : n ≠ k := by omega
  have hn1 : n ≠ n + 1 := by omega
  have hn1k : n + 1 ≠ k := by omega
  refine ⟨?_, ?_⟩
  · funext i
    simp only [tPass, if_neg hnk', if_neg hn1, if_neg hn1k, Pi.add_apply, Matrix.mulVec,
      dotProduct, GammaPass]
    unfold expHitTime
    simp_rw [g72ma_at]
    have hd := g72ma_decAV Q (fun x : ℕ × ι => x.1 ≤ n) (fun z : ℕ × ι => z.1 = n + 1)
      (fun w => w ∉ (level k : Set (ℕ × ι))) (fun w => w ∉ (level (n + 1) : Set (ℕ × ι))) hstep
    rw [tsum_congr fun t => hd t (n, i) le_rfl, ENNReal.tsum_add]
    congr 1
    have hsw := g72ma_swap (fun z : ℕ × ι => z.1 = n + 1)
      (fun z s => g72ma_PS Q (n, i) s z (fun w => w ∉ (level (n + 1) : Set (ℕ × ι))))
      (fun z u => g72ma_AV Q z (fun w => w ∉ (level k : Set (ℕ × ι))) (u - 1))
    simp only [Nat.add_sub_cancel] at hsw
    simp_rw [show ∀ t s : ℕ, t - s - 1 = t - (s + 1) from fun t s => by omega] at hsw
    rw [hsw, g72ma_levn, tsum_fintype]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [g72ma_hd Q _ _ _ (by simp [level])]
  · funext i j
    simp only [GammaPass, if_neg hnk', if_neg hn1, if_neg hn1k, Matrix.mul_apply]
    rw [g72ma_hd Q _ _ _ (by simp [level])]
    have hc := g72ma_conv2 Q (fun x : ℕ × ι => x.1 ≤ n) (fun z : ℕ × ι => z.1 = n + 1)
      (fun w => w ∉ (level k : Set (ℕ × ι))) (fun w => w ∉ (level (n + 1) : Set (ℕ × ι))) hstep
      (k, j) (fun x hx => by
        by_contra h
        have := g72ma_fup M P₀₀ A₀ A₁ A₂ P_MM x (k, j) h
        simp only at this hx; omega)
    rw [tsum_congr fun t => hc t (n, i) le_rfl]
    have hsw := g72ma_swap (fun z : ℕ × ι => z.1 = n + 1)
      (fun z s => g72ma_PS Q (n, i) s z (fun w => w ∉ (level (n + 1) : Set (ℕ × ι))))
      (fun z u => g72ma_PS Q z u (k, j) (fun w => w ∉ (level k : Set (ℕ × ι))))
    rw [hsw, g72ma_levn, tsum_fintype]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [g72ma_hd Q _ _ _ (by simp [level]), g72ma_hd Q _ _ _ (by simp [level])]
