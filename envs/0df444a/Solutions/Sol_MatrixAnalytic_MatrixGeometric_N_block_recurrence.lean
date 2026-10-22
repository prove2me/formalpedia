-- Prove2me | solution 1 for MatrixAnalytic.MatrixGeometric.N_block_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:14:52.254516+00:00
-- url     : https://prove2.me/submissions/e2c2804e-17f6-449f-8f59-bfe5283ad4db

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

open scoped ENNReal
open MatrixAnalytic.MatrixGeometric

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

lemma g72mab_eva (n : ℕ) (x y : ℕ × ι) (hy : n < y.1) :
    expVisitsAvoid (qbdP B A₀ A₁ A₂) (levelsUpTo n) x y =
      ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) x t y (fun z => n < z.1) := by
  classical
  unfold expVisitsAvoid g72mab_PS
  refine tsum_congr fun t => tsum_congr fun ω => ?_
  have hc : (ω 0 = x ∧ ω (Fin.last t) = y ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ levelsUpTo n) ↔
      (ω 0 = x ∧ ω (Fin.last t) = y ∧
        ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → n < (ω m).1) := by
    simp only [levelsUpTo, Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun m hm _ => h3 m hm⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2]; exact hy
      · exact h3 m hm hl
  by_cases h : ω 0 = x ∧ ω (Fin.last t) = y ∧
      ∀ m : Fin (t + 1), m ≠ 0 → m ≠ Fin.last t → n < (ω m).1
  · rw [if_pos (hc.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

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

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) :
    (∀ k : ℕ, 1 ≤ k →
      matNblock (qbdP B A₀ A₁ A₂) n (k + 1) =
        matMulE (matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1) (ennMat A₀))
          (matNblock (qbdP B A₀ A₁ A₂) n k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      matNblock (qbdP B A₀ A₁ A₂) n k =
          matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1)
            (matPowE (matMulE (ennMat A₀) (matNblock (qbdP B A₀ A₁ A₂) n 1)) (k - 1)) ∧
        matNblock (qbdP B A₀ A₁ A₂) n k =
          matMulE (matNblock (qbdP B A₀ A₁ A₂) n 1)
            (matPowE (matR (qbdP B A₀ A₁ A₂) n) (k - 1))) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  -- N_{1k} as path sums
  have hN : ∀ k i j, 1 ≤ k → matNblock P n k i j =
      ∑' t, g72mab_PS P (n + 1, i) t (n + k, j) (fun z => n < z.1) := by
    intro k i j hk
    exact g72mab_eva B A₀ A₁ A₂ n _ _ (by simp; omega)
  -- step from level n+1 into the rest
  have hstepN : ∀ (k : ℕ) (l j : ι), 1 ≤ k →
      ∑' u, g72mab_PS P (n + 1, l) (u + 1) (n + k + 1, j) (fun z => n + 1 < z.1) =
        ∑' l', ENNReal.ofReal (A₀ l l') * matNblock P n k l' j := by
    intro k l j hk
    simp_rw [g72mab_PS_cons P (n + 1, l)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_prod', tsum_eq_single (n + 2)]
    · refine tsum_congr fun l' => ?_
      have hP2 : P (n + 1, l) (n + 2, l') = A₀ l l' := by simp [hPd, qbdP]
      rw [hP2, hN k l' j hk]
      congr 1
      refine tsum_congr fun u => ?_
      rw [if_pos (Or.inr (by simp))]
      have := g72mab_PS_shiftN B A₀ A₁ A₂ n (n + 1) (n + k) l' j (by omega) u
      rw [← hPd] at this
      rw [← this]
    · intro m hm
      refine ENNReal.tsum_eq_zero.mpr fun l' => ?_
      by_cases hPz : P (n + 1, l) (m, l') = 0
      · simp [hPz]
      have := g72mab_qnz B A₀ A₁ A₂ _ _ hPz
      simp only at this
      rw [ENNReal.tsum_eq_zero.mpr]
      · simp
      intro u
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg]
        intro h; simp only [Prod.mk.injEq] at h; omega
      · rw [if_neg]
        rintro (hu' | hu')
        · omega
        · simp only at hu'; omega
  have hR : matR P n = matMulE (ennMat A₀) (matNblock P n 1) := by
    funext i j
    unfold matR
    have hev := g72mab_eva B A₀ A₁ A₂ n (n, i) (n + 1, j) (by simp)
    rw [← hPd] at hev
    rw [hev, tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero,
      if_neg (by simp [Prod.ext_iff]), zero_add]
    simp_rw [g72mab_PS_cons P (n, i)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    unfold matMulE ennMat
    rw [ENNReal.tsum_prod', tsum_eq_single (n + 1)]
    · refine tsum_congr fun l => ?_
      have hP1 : P (n, i) (n + 1, l) = A₀ i l := by
        rw [hPd]; unfold qbdP; dsimp only; split_ifs <;> first | rfl | omega | simp_all
      rw [hP1, hN 1 l j le_rfl]
      congr 1
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by simp))]
    · intro m hm
      refine ENNReal.tsum_eq_zero.mpr fun l => ?_
      by_cases hPz : P (n, i) (m, l) = 0
      · simp [hPz]
      have := g72mab_qnz B A₀ A₁ A₂ _ _ hPz
      simp only at this
      rw [ENNReal.tsum_eq_zero.mpr]
      · simp
      intro u
      rcases Nat.eq_zero_or_pos u with hu | hu
      · subst hu
        rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg]
        intro h; simp only [Prod.mk.injEq] at h; omega
      · rw [if_neg]
        rintro (hu' | hu')
        · omega
        · simp only at hu'; omega
  have hstep3 : ∀ w y : ℕ × ι, (fun z : ℕ × ι => n + 2 ≤ z.1) y → P w y ≠ 0 →
      ((fun z : ℕ × ι => z.1 = n + 1) w ∧ (fun z : ℕ × ι => n < z.1) w ∧
        ¬ (fun z : ℕ × ι => n + 1 < z.1) w) ∨
      ((fun z : ℕ × ι => n + 1 < z.1) w ∧ (fun z : ℕ × ι => n < z.1) w ∧
        (fun z : ℕ × ι => n + 2 ≤ z.1) w ∧ ¬ (fun z : ℕ × ι => z.1 = n + 1) w) ∨
      (¬ (fun z : ℕ × ι => n < z.1) w ∧ ¬ (fun z : ℕ × ι => n + 1 < z.1) w ∧
        ¬ (fun z : ℕ × ι => z.1 = n + 1) w) := by
    intro w y hy hw
    have := g72mab_qnz B A₀ A₁ A₂ _ _ hw
    simp only at hy ⊢
    omega
  have h1 : ∀ k, 1 ≤ k → matNblock P n (k + 1) =
      matMulE (matMulE (matNblock P n 1) (ennMat A₀)) (matNblock P n k) := by
    intro k hk
    funext i j
    rw [hN (k + 1) i j (by omega), tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero,
      if_neg (by simp [Prod.ext_iff]; omega), zero_add]
    have hc := g72mab_conv3 P (fun z : ℕ × ι => n + 2 ≤ z.1) (fun z : ℕ × ι => z.1 = n + 1)
      (fun z : ℕ × ι => n < z.1) (fun z : ℕ × ι => n + 1 < z.1) (n + 1, i) rfl hstep3
    rw [tsum_congr fun t => hc t (n + (k + 1), j) (by simp; omega)]
    have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = n + 1 then
        g72mab_PS P (n + 1, i) s z (fun z => n < z.1) *
          g72mab_PS P z (t + 1 - s) (n + (k + 1), j) (fun z => n + 1 < z.1) else 0) =
        ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = n + 1 then
        g72mab_PS P (n + 1, i) s z (fun z => n < z.1) *
          (fun z u => g72mab_PS P z (u + 1) (n + (k + 1), j) (fun z => n + 1 < z.1)) z (t - s)
          else 0) := by
      intro t
      refine Finset.sum_congr rfl fun s hs => ?_
      have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      rw [show t + 1 - s = t - s + 1 by omega]
    refine (tsum_congr e).trans ((g72mab_swap0 (fun z : ℕ × ι => z.1 = n + 1)
      (fun z s => g72mab_PS P (n + 1, i) s z (fun z => n < z.1))
      (fun z u => g72mab_PS P z (u + 1) (n + (k + 1), j) (fun z => n + 1 < z.1))).trans ?_)
    rw [g72mab_levn]
    have hN1 : ∀ l, (∑' s, g72mab_PS P (n + 1, i) s (n + 1, l) (fun z => n < z.1)) =
        matNblock P n 1 i l := fun l => (hN 1 i l le_rfl).symm
    simp_rw [hN1, show n + (k + 1) = n + k + 1 by ring, hstepN k _ j hk]
    unfold matMulE ennMat
    simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun l => tsum_congr fun l' => ?_
    ring
  refine ⟨h1, fun k hk => ?_⟩
  have h2 : matNblock P n k =
      matMulE (matNblock P n 1) (matPowE (matMulE (ennMat A₀) (matNblock P n 1)) (k - 1)) := by
    induction k, hk using Nat.le_induction with
    | base => simp only [Nat.sub_self]; exact (g72mab_mm_one _).symm
    | succ k hk ih =>
      rw [h1 k hk, ih, show k + 1 - 1 = (k - 1) + 1 by omega, ← g72mab_pow_succ']
      simp only [g72mab_mm_assoc]
  exact ⟨h2, by rw [h2, hR]⟩
