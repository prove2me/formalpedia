-- Prove2me | solution 1 for MatrixAnalytic.Spectral.xi_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:02:25.629378+00:00
-- url     : https://prove2.me/submissions/eee8344b-8aec-4b30-ab94-02398e7d9d08

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix
open MatrixAnalytic.Spectral

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

end UGRgen
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
lemma g72mab_GN {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ) (m : ℕ)
    (i j : ι) :
    ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, i) (t + 1) (m, j) (fun z => m < z.1) =
      ∑' l, (∑' s, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, i) s (m + 1, l) (fun z => m < z.1)) *
        ENNReal.ofReal (A₂ l j) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hqnz : ∀ x w : ℕ × ι, P x w ≠ 0 → w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 :=
    fun x w h => g72mab_qnz B A₀ A₁ A₂ x w h
  have hst : ∀ w y : ℕ × ι, (fun z : ℕ × ι => m ≤ z.1) y → P w y ≠ 0 →
      ((fun z : ℕ × ι => z.1 = m + 1) w ∧ (fun z : ℕ × ι => m < z.1) w ∧
          ¬ (fun z : ℕ × ι => m + 1 < z.1) w) ∨
      ((fun z : ℕ × ι => m + 1 < z.1) w ∧ (fun z : ℕ × ι => m < z.1) w ∧
          (fun z : ℕ × ι => m ≤ z.1) w ∧ ¬ (fun z : ℕ × ι => z.1 = m + 1) w) ∨
      (¬ (fun z : ℕ × ι => m < z.1) w ∧ ¬ (fun z : ℕ × ι => m + 1 < z.1) w ∧
          ¬ (fun z : ℕ × ι => z.1 = m + 1) w) := by
    intro w y _ _
    simp only
    omega
  have hb : ∀ (l j : ι) (u : ℕ), g72mab_PS P (m + 1, l) (u + 1) (m, j) (fun z => m + 1 < z.1) =
      if u = 0 then ENNReal.ofReal (A₂ l j) else 0 := by
    intro l j u
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; rw [g72mab_PS_one, if_pos rfl]; simp [hPd, qbdP, show m ≠ m + 1 + 1 by omega]
    · rw [if_neg (by omega), g72mab_PS_snoc]
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      by_cases hw : m + 1 < w.1
      · have : P w (m, j) = 0 := by
          by_contra h; have := hqnz w (m, j) h; simp at this; omega
        simp [this]
      · rw [if_neg (by omega)]; simp
  rw [tsum_congr fun t => g72mab_conv3 P (fun z : ℕ × ι => m ≤ z.1) (fun z : ℕ × ι => z.1 = m + 1)
    (fun z : ℕ × ι => m < z.1) (fun z : ℕ × ι => m + 1 < z.1) (m + 1, i) rfl hst t (m, j) le_rfl]
  have e : ∀ t, ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = m + 1 then
      g72mab_PS P (m + 1, i) s z (fun z => m < z.1) *
        g72mab_PS P z (t + 1 - s) (m, j) (fun z => m + 1 < z.1) else 0) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = m + 1 then
      g72mab_PS P (m + 1, i) s z (fun z => m < z.1) *
        (fun z u => g72mab_PS P z (u + 1) (m, j) (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro t
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  rw [tsum_congr e, g72mab_swap0 (fun z : ℕ × ι => z.1 = m + 1)
    (fun z s => g72mab_PS P (m + 1, i) s z (fun z => m < z.1))
    (fun z u => g72mab_PS P z (u + 1) (m, j) (fun z => m + 1 < z.1)), g72mab_levn]
  refine tsum_congr fun l => ?_
  simp only [hb]
  rw [tsum_eq_single 0 (fun u hu => if_neg hu), if_pos rfl]


section XiQ
variable {ι : Type*} [Countable ι] [DecidableEq ι] (B A₀ A₁ A₂ : ι → ι → ℝ)

lemma g72mab_hst (m : ℕ) : ∀ w y : ℕ × ι, (fun z : ℕ × ι => m ≤ z.1) y →
      qbdP B A₀ A₁ A₂ w y ≠ 0 →
      ((fun z : ℕ × ι => z.1 = m + 1) w ∧ (fun z : ℕ × ι => m < z.1) w ∧
          ¬ (fun z : ℕ × ι => m + 1 < z.1) w) ∨
      ((fun z : ℕ × ι => m + 1 < z.1) w ∧ (fun z : ℕ × ι => m < z.1) w ∧
          (fun z : ℕ × ι => m ≤ z.1) w ∧ ¬ (fun z : ℕ × ι => z.1 = m + 1) w) ∨
      (¬ (fun z : ℕ × ι => m < z.1) w ∧ ¬ (fun z : ℕ × ι => m + 1 < z.1) w ∧
          ¬ (fun z : ℕ × ι => z.1 = m + 1) w) := by
  intro w y _ _
  simp only
  omega

lemma g72mab_Neq (m : ℕ) (i j : ι) :
    ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, i) t (m + 1, j) (fun z => m < z.1) =
      (if i = j then 1 else 0) + ∑' l,
        (∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, i) t (m + 1, l) (fun z => m < z.1)) *
        ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, l) (t + 1) (m + 1, j) (fun z => m + 1 < z.1) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hconvN : ∀ t, g72mab_PS P (m + 1, i) (t + 1) (m + 1, j) (fun z => m < z.1) =
      ∑ s ∈ Finset.range (t + 1), ∑' z : ℕ × ι, (if z.1 = m + 1 then
        g72mab_PS P (m + 1, i) s z (fun z => m < z.1) *
          (fun z u => g72mab_PS P z (u + 1) (m + 1, j) (fun z => m + 1 < z.1)) z (t - s) else 0) := by
    intro t
    rw [g72mab_conv3 P (fun z : ℕ × ι => m ≤ z.1) (fun z : ℕ × ι => z.1 = m + 1)
      (fun z : ℕ × ι => m < z.1) (fun z : ℕ × ι => m + 1 < z.1) (m + 1, i) rfl
      (g72mab_hst B A₀ A₁ A₂ m) t (m + 1, j) (Nat.le_succ m)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : s ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show t + 1 - s = t - s + 1 by omega]
  rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero]
  congr 1
  · simp
  rw [tsum_congr hconvN, g72mab_swap0 (fun z : ℕ × ι => z.1 = m + 1)
    (fun z s => g72mab_PS P (m + 1, i) s z (fun z => m < z.1))
    (fun z u => g72mab_PS P z (u + 1) (m + 1, j) (fun z => m + 1 < z.1)), g72mab_levn]

lemma g72mab_UAG (m : ℕ) (i j : ι) :
    ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, i) (t + 1) (m + 1, j) (fun z => m + 1 < z.1) =
      ENNReal.ofReal (A₁ i j) + ∑' k, ENNReal.ofReal (A₀ i k) *
        ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (m + 1, k) (t + 1) (m, j) (fun z => m < z.1) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hqnz : ∀ x w : ℕ × ι, P x w ≠ 0 → w.1 ≤ x.1 + 1 ∧ x.1 ≤ w.1 + 1 :=
    fun x w h => g72mab_qnz B A₀ A₁ A₂ x w h
  simp_rw [g72mab_PS_cons P (m + 1, i)]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have key : ∀ z : ℕ × ι, ENNReal.ofReal (P (m + 1, i) z) * ∑' t, (if t = 0 ∨ m + 1 < z.1 then
      g72mab_PS P z t (m + 1, j) (fun z => m + 1 < z.1) else 0) =
      (if z.1 = m + 1 then ENNReal.ofReal (A₁ i z.2) * (if z.2 = j then 1 else 0) else 0) +
      (if z.1 = m + 1 + 1 then ENNReal.ofReal (A₀ i z.2) *
        ∑' t, g72mab_PS P (m + 1, z.2) (t + 1) (m, j) (fun z => m < z.1) else 0) := by
    intro z
    obtain ⟨k, l⟩ := z
    simp only
    by_cases h1 : k = m + 1
    · subst h1
      have c1 : ¬ (m + 1 = m + 1 + 1) := by omega
      have hP' : P (m + 1, i) (m + 1, l) = A₁ i l := by simp [hPd, qbdP]
      simp only [c1, eq_self_iff_true, if_true, if_false, add_zero, lt_irrefl, or_false, hP']
      rw [tsum_eq_single 0 (fun t ht => if_neg ht), if_pos rfl, g72mab_PS_zero]
      simp
    by_cases h2 : k = m + 1 + 1
    · subst h2
      have c1 : ¬ (m + 1 + 1 = m + 1) := by omega
      have hP' : P (m + 1, i) (m + 1 + 1, l) = A₀ i l := by simp [hPd, qbdP]
      simp only [c1, eq_self_iff_true, if_true, if_false, zero_add, hP']
      congr 1
      rw [tsum_eq_zero_add' ENNReal.summable, if_pos (Or.inl rfl), g72mab_PS_zero,
        if_neg (by simp), zero_add]
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by omega))]
      exact g72mab_PS_shiftN B A₀ A₁ A₂ m (m + 1) m l j (by omega) (t + 1)
    · rw [if_neg h1, if_neg h2, add_zero]
      by_cases hle : k ≤ m
      · rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
        intro t
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg]
          intro h; simp only [Prod.mk.injEq] at h; omega
        · rw [if_neg (by omega)]
      · have : P (m + 1, i) (k, l) = 0 := by
          by_contra h; have := hqnz _ _ h; simp only at this; omega
        simp [this]
  rw [tsum_congr key, ENNReal.tsum_add, g72mab_levn, g72mab_levn]
  congr 1
  simp

lemma g72mab_R0 (i j : ι) :
    ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (0, i) t (1, j) (fun z => 0 < z.1) =
      ∑' l, ENNReal.ofReal (A₀ i l) *
        ∑' t, g72mab_PS (qbdP B A₀ A₁ A₂) (1, l) t (1, j) (fun z => 0 < z.1) := by
  classical
  set P := qbdP B A₀ A₁ A₂ with hPd
  rw [tsum_eq_zero_add' ENNReal.summable, g72mab_PS_zero, if_neg (by simp), zero_add]
  simp_rw [g72mab_PS_cons P (0, i)]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have key : ∀ z : ℕ × ι, ENNReal.ofReal (P (0, i) z) * ∑' t, (if t = 0 ∨ 0 < z.1 then
      g72mab_PS P z t (1, j) (fun z => 0 < z.1) else 0) =
      if z.1 = 1 then ENNReal.ofReal (A₀ i z.2) *
        ∑' t, g72mab_PS P (1, z.2) t (1, j) (fun z => 0 < z.1) else 0 := by
    intro z
    obtain ⟨k, l⟩ := z
    simp only
    by_cases h1 : k = 1
    · subst h1
      have hP' : P (0, i) (1, l) = A₀ i l := by simp [hPd, qbdP]
      rw [if_pos rfl, hP']
      congr 1
      refine tsum_congr fun t => ?_
      rw [if_pos (Or.inr (by omega))]
    · rw [if_neg h1]
      by_cases h0 : k = 0
      · subst h0
        rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
        intro t
        rcases Nat.eq_zero_or_pos t with ht | ht
        · subst ht
          rw [if_pos (Or.inl rfl), g72mab_PS_zero, if_neg]
          intro h; simp only [Prod.mk.injEq] at h; omega
        · rw [if_neg (by omega)]
      · have : P (0, i) (k, l) = 0 := by simp [hPd, qbdP, h0, h1]
        simp [this]
  rw [tsum_congr key, g72mab_levn]
end XiQ

noncomputable def g72mab_mm {ι : Type*} (X Y : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k, X i k * Y k j

lemma g72mab_mmA {ι : Type*} [Countable ι] (X Y Z : ι → ι → ℝ≥0∞) :
    g72mab_mm (g72mab_mm X Y) Z = g72mab_mm X (g72mab_mm Y Z) := by
  funext i j
  unfold g72mab_mm
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  ring

lemma g72mab_mmL {ι : Type*} [Countable ι] (X Y Z : ι → ι → ℝ≥0∞) :
    g72mab_mm (X + Y) Z = g72mab_mm X Z + g72mab_mm Y Z := by
  funext i j
  simp only [g72mab_mm, Pi.add_apply, add_mul, ENNReal.tsum_add]

lemma g72mab_mmR {ι : Type*} [Countable ι] (X Y Z : ι → ι → ℝ≥0∞) :
    g72mab_mm X (Y + Z) = g72mab_mm X Y + g72mab_mm X Z := by
  funext i j
  simp only [g72mab_mm, Pi.add_apply, mul_add, ENNReal.tsum_add]

lemma g72mab_mm1 {ι : Type*} [Countable ι] [DecidableEq ι] (X : ι → ι → ℝ≥0∞) :
    g72mab_mm X (fun i j => if i = j then 1 else 0) = X := by
  funext i j
  unfold g72mab_mm
  rw [tsum_eq_single j]
  · simp
  · intro b hb; simp [hb]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      ∀ x : ℂ, XiAt A₀ A₁ A₂ x =
        (x • (1 : Matrix ι ι ℂ) - matRc (qbdP B A₀ A₁ A₂)) * PhiR A₁ A₂ (matRc (qbdP B A₀ A₁ A₂)) x
      := by
  classical
  have hP0' := hP.1
  have hrow' := hP.2
  have hRN := g72mab_R0 B A₀ A₁ A₂
  have hNeq := g72mab_Neq B A₀ A₁ A₂ 0
  have hUAG := g72mab_UAG B A₀ A₁ A₂ 0
  have hGN := g72mab_GN B A₀ A₁ A₂ 0
  set P := qbdP B A₀ A₁ A₂ with hPd
  have hP0 : ∀ x y, 0 ≤ P x y := hP0'
  have hrow : ∀ z, ∑' y, ENNReal.ofReal (P z y) = 1 := by
    intro z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hP0 z) (hrow' z).summable, (hrow' z).tsum_eq,
      ENNReal.ofReal_one]
  have hA0nn : ∀ i j, 0 ≤ A₀ i j := fun i j => by simpa [hPd, qbdP] using hP0 (1, i) (2, j)
  have hA1nn : ∀ i j, 0 ≤ A₁ i j := fun i j => by simpa [hPd, qbdP] using hP0 (1, i) (1, j)
  have hA2nn : ∀ i j, 0 ≤ A₂ i j := fun i j => by simpa [hPd, qbdP] using hP0 (1, i) (0, j)
  have hReq : ∀ i j, matR P i j = ∑' t, g72mab_PS P (0, i) t (1, j) (fun z => 0 < z.1) := by
    intro i j
    unfold matR expVisitsAvoid g72mab_PS
    refine tsum_congr fun t => tsum_congr fun ω => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exfalso; apply h2
      refine ⟨h1.1, h1.2.1, fun m hm _ => ?_⟩
      have := h1.2.2 m hm; simp only [level, Set.mem_setOf_eq] at this; omega
    · exfalso; apply h1
      refine ⟨h2.1, h2.2.1, fun m hm => ?_⟩
      by_cases hl : m = Fin.last t
      · rw [hl, h2.2.1]; simp [level]
      · have := h2.2.2 m hm hl; simp only [level, Set.mem_setOf_eq]; omega
    · rfl
  have hconv : ∀ (x0 : ℕ × ι) T, ENNReal.ofReal (returnTailC P x0 T) =
      g72mab_AV P x0 (fun z => z ≠ x0) T := by
    intro x0 T
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
  have hfin : ∀ i j, matR P i j ≠ ⊤ := by
    intro i j
    have hle : matR P i j ≤ ∑' t, ENNReal.ofReal (returnTailC P (0, i) t) := by
      rw [hReq]
      refine ENNReal.tsum_le_tsum fun t => ?_
      rw [hconv]
      rcases t with _ | t
      · rw [g72mab_PS_zero, if_neg (by simp)]; exact bot_le
      · rw [g72mab_AV_eq]
        refine le_trans ?_ (ENNReal.le_tsum (1, j))
        rw [if_pos (by simp)]
        exact g72mab_PS_mono P _ _ (fun z hz h => by rw [h] at hz; simp at hz) _ _ _
    refine ne_top_of_le_ne_top ?_ hle
    have hnn : ∀ t, 0 ≤ returnTailC P (0, i) t := by
      intro t
      unfold returnTailC setAvoidTailC
      refine tsum_nonneg fun ω => ?_
      split_ifs
      · exact Finset.prod_nonneg fun s _ => hP0 _ _
      · exact le_rfl
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (hpos (0, i))]
    exact ENNReal.ofReal_ne_top
  refine ⟨hfin, ?_⟩
  -- ENNReal identity
  set E0 : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A₀ i j) with hE0
  set E1 : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A₁ i j) with hE1
  set E2 : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A₂ i j) with hE2
  set Nf : ι → ι → ℝ≥0∞ := fun i j =>
    ∑' t, g72mab_PS P (0 + 1, i) t (0 + 1, j) (fun z => 0 < z.1) with hNf
  set Uf : ι → ι → ℝ≥0∞ := fun i j =>
    ∑' t, g72mab_PS P (0 + 1, i) (t + 1) (0 + 1, j) (fun z => 0 + 1 < z.1) with hUf
  set Gf : ι → ι → ℝ≥0∞ := fun i j =>
    ∑' t, g72mab_PS P (0 + 1, i) (t + 1) (0, j) (fun z => 0 < z.1) with hGf
  set Rm : ι → ι → ℝ≥0∞ := fun i j => matR P i j with hRm
  have h1 : Rm = g72mab_mm E0 Nf := funext fun i => funext fun j => (hReq i j).trans (hRN i j)
  have h2 : Nf = (fun i j => if i = j then 1 else 0) + g72mab_mm Nf Uf :=
    funext fun i => funext fun j => hNeq i j
  have h3 : Uf = E1 + g72mab_mm E0 Gf := funext fun i => funext fun j => hUAG i j
  have h4 : Gf = g72mab_mm Nf E2 := funext fun i => funext fun j => hGN i j
  have hE : Rm = E0 + g72mab_mm Rm E1 + g72mab_mm (g72mab_mm Rm Rm) E2 := by
    have : Rm = E0 + g72mab_mm Rm Uf := by
      conv_lhs => rw [h1, h2]
      rw [g72mab_mmR, g72mab_mm1, ← g72mab_mmA, ← h1]
    conv_lhs => rw [this]
    rw [h3, g72mab_mmR, h4, ← g72mab_mmA E0 Nf E2, ← h1, ← g72mab_mmA, add_assoc]
  intro x
  have hreal : ∀ i j, (matR P i j).toReal = A₀ i j + ∑ l, (matR P i l).toReal * A₁ l j +
      ∑ l, (∑ k, (matR P i k).toReal * (matR P k l).toReal) * A₂ l j := by
    intro i j
    have e := congrFun (congrFun hE i) j
    simp only [hRm, hE0, hE1, hE2, Pi.add_apply, g72mab_mm, tsum_fintype] at e
    rw [e]
    simp [ENNReal.toReal_add, ENNReal.toReal_sum, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
      hA0nn, hA1nn, hA2nn, ENNReal.add_eq_top, ENNReal.sum_eq_top, ENNReal.mul_eq_top, hfin]
  have hRc : matRc P = cMat A₀ + matRc P * cMat A₁ + matRc P * matRc P * cMat A₂ := by
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, matRc, cMat, Matrix.of_apply]
    rw [hreal i j]
    push_cast
    ring
  have hA0 : cMat A₀ = matRc P - matRc P * cMat A₁ - matRc P * matRc P * cMat A₂ := by
    rw [sub_right_comm]; exact eq_sub_of_add_eq (eq_sub_of_add_eq hRc.symm)
  unfold XiAt PhiR
  rw [hA0]
  simp only [sub_mul, mul_add, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_sub, Matrix.mul_assoc, smul_smul]
  module
