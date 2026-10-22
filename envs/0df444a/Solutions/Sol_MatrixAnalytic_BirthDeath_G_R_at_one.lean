-- Prove2me | solution 1 for MatrixAnalytic.BirthDeath.G_R_at_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:37:03.581+00:00
-- url     : https://prove2.me/submissions/540b6c4a-5994-4812-9b21-3d6a0ad65d91

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage
open MatrixAnalytic.BirthDeath

open scoped ENNReal

lemma g71y_pw_cons (P : ℕ → ℕ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℕ) (k : ℕ) :
    pathWeightC P (Fin.cons k ω : Fin (n + 2) → ℕ) = P k (ω 0) * pathWeightC P ω := by
  unfold pathWeightC
  rw [Fin.prod_univ_succ]
  congr 1

lemma g71y_pw_snoc (P : ℕ → ℕ → ℝ) {n : ℕ} (ω : Fin (n + 1) → ℕ) (k : ℕ) :
    pathWeightC P (Fin.snoc ω k : Fin (n + 2) → ℕ) = pathWeightC P ω * P (ω (Fin.last n)) k := by
  unfold pathWeightC
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g71y_pw_nonneg (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) {n : ℕ} (ω : Fin (n + 1) → ℕ) :
    0 ≤ pathWeightC P ω :=
  Finset.prod_nonneg fun _ _ => h0 _ _

lemma g71y_tsum_snoc {n : ℕ} (f : (Fin (n + 2) → ℕ) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → ℕ, f ω = ∑' ω : Fin (n + 1) → ℕ, ∑' k : ℕ, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => ℕ)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g71y_tsum_cons {n : ℕ} (f : (Fin (n + 2) → ℕ) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → ℕ, f ω = ∑' k : ℕ, ∑' ω : Fin (n + 1) → ℕ, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => ℕ)).tsum_eq, ENNReal.tsum_prod']
  rfl

lemma g71y_toReal_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ∑' a, f a = (∑' a, ENNReal.ofReal (f a)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun a => (ENNReal.toReal_ofReal (hf a)).symm

open Classical in
noncomputable def g71y_SAE (P : ℕ → ℕ → ℝ) (x : ℕ) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → ℕ,
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0 then ENNReal.ofReal (pathWeightC P ω) else 0

open Classical in
noncomputable def g71y_gE (P : ℕ → ℕ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (k + 1) → ℕ,
    if ω 0 = 1 ∧ ω (Fin.last k) = 0 ∧ (∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → 0 < ω m)
    then ENNReal.ofReal (pathWeightC P ω) else 0

lemma g71y_rowsum (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (y : ℕ) :
    ∑' x, ENNReal.ofReal (P y x) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => hP.stochastic.1 y x)
    (hP.stochastic.2 y).summable, (hP.stochastic.2 y).tsum_eq, ENNReal.ofReal_one]

lemma g71y_step (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (t : ℕ) :
    g71y_SAE P 1 (t + 1) + g71y_gE P (t + 1) = g71y_SAE P 1 t := by
  classical
  have h0 := hP.stochastic.1
  unfold g71y_SAE g71y_gE
  rw [g71y_tsum_snoc, g71y_tsum_snoc, ← ENNReal.tsum_add]
  refine tsum_congr fun ω => ?_
  rw [← ENNReal.tsum_add]
  have hz : ∀ k, (Fin.snoc ω k : Fin (t + 2) → ℕ) 0 = ω 0 := fun k => by
    have : (0 : Fin (t + 2)) = (0 : Fin (t + 1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  have hA : ∀ k, (∀ i : Fin (t + 2), i ≠ 0 → (Fin.snoc ω k : Fin (t + 2) → ℕ) i ≠ 0) ↔
      (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0) ∧ k ≠ 0 := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have e1 : ∀ m : Fin (t + 1), (m.castSucc = 0) ↔ m = 0 := fun m => by
      constructor
      · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
      · rintro rfl; rfl
    have e2 : Fin.last (t + 1) ≠ 0 := by simp [Fin.ext_iff]
    simp only [ne_eq, e1, e2, not_false_eq_true, true_implies]
  have hB : ∀ k, (∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) →
      0 < (Fin.snoc ω k : Fin (t + 2) → ℕ) m) ↔ (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0) := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff,
      and_true]
    refine forall_congr' fun m => ?_
    have e1 : (m.castSucc = 0) ↔ m = 0 := by
      constructor
      · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
      · rintro rfl; rfl
    have e2 : m.castSucc ≠ Fin.last (t+1) := Fin.castSucc_ne_last m
    simp only [e1, e2, not_false_eq_true, true_implies, Nat.pos_iff_ne_zero]
  simp_rw [hz, hA, hB, Fin.snoc_last, g71y_pw_snoc]
  by_cases hc : ω 0 = 1 ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0
  · rw [if_pos hc]
    have : ∀ k, ((if ω 0 = 1 ∧ (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0) ∧ k ≠ 0 then
        ENNReal.ofReal (pathWeightC P ω * P (ω (Fin.last t)) k) else 0) +
        if ω 0 = 1 ∧ k = 0 ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0 then
        ENNReal.ofReal (pathWeightC P ω * P (ω (Fin.last t)) k) else 0) =
        ENNReal.ofReal (pathWeightC P ω) * ENNReal.ofReal (P (ω (Fin.last t)) k) := by
      intro k
      rw [ENNReal.ofReal_mul (g71y_pw_nonneg P h0 ω)]
      by_cases hk : k = 0
      · rw [if_neg (by tauto), if_pos ⟨hc.1, hk, hc.2⟩, zero_add]
      · rw [if_pos ⟨hc.1, hc.2, hk⟩, if_neg (by tauto), add_zero]
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, g71y_rowsum P hP, mul_one]
  · rw [if_neg hc]
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [if_neg (by tauto), if_neg (by tauto), add_zero]

lemma g71y_mass (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (t : ℕ) :
    g71y_SAE P 1 t + ∑ k ∈ Finset.range t, g71y_gE P (k + 1) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g71y_SAE
    rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single 1]
    · simp [pathWeightC]
    · intro b hb; simp [hb]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g71y_gE P (t + 1)), ← add_assoc,
      add_comm (g71y_gE P (t + 1)), g71y_step P hP t, ih]


open Classical in
noncomputable def g71y_PS (P : ℕ → ℕ → ℝ) (x L y : ℕ) (A : ℕ → Prop) : ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → ℕ,
    if ω 0 = x ∧ ω (Fin.last L) = y ∧ ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m)
    then ENNReal.ofReal (pathWeightC P ω) else 0

lemma g71y_taboo_eq (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) (a i j k : ℕ) :
    tabooProb P a i j k = (g71y_PS P i k j (fun s => a < s)).toReal := by
  unfold tabooProb g71y_PS
  rw [g71y_toReal_tsum _ (fun ω => by split_ifs; exacts [g71y_pw_nonneg P h0 ω, le_rfl])]
  congr 1
  refine tsum_congr fun ω => ?_
  split_ifs <;> simp

lemma g71y_ite_tsum {α : Type*} (c : Prop) [Decidable c] (f : α → ℝ≥0∞) :
    (if c then ∑' i, f i else 0) = ∑' i, if c then f i else 0 := by
  split_ifs <;> simp

lemma g71y_PS_zero (P : ℕ → ℕ → ℝ) (x y : ℕ) (A : ℕ → Prop) :
    g71y_PS P x 0 y A = if x = y then 1 else 0 := by
  classical
  unfold g71y_PS
  rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [tsum_eq_single x]
    · simp [pathWeightC]
    · intro b hb; simp [hb]
  · rw [if_neg hxy]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hxy (h1.symm.trans (by simpa using h2))

lemma g71y_cond_cons {L : ℕ} (x y : ℕ) (A : ℕ → Prop) (ω : Fin (L + 1) → ℕ) :
    ((Fin.cons x ω : Fin (L + 2) → ℕ) 0 = x ∧ (Fin.cons x ω : Fin (L + 2) → ℕ) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.cons x ω : Fin (L + 2) → ℕ) m)) ↔
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

lemma g71y_PS_cons (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) (x L y : ℕ) (A : ℕ → Prop)
    [DecidablePred A] :
    g71y_PS P x (L + 1) y A =
      ∑' z, ENNReal.ofReal (P x z) * (if L = 0 ∨ A z then g71y_PS P z L y A else 0) := by
  classical
  unfold g71y_PS
  rw [g71y_tsum_cons, tsum_eq_single x]
  · simp_rw [g71y_ite_tsum, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · have hcc := g71y_cond_cons x y A ω
      rw [g71y_pw_cons, ENNReal.ofReal_mul (h0 _ _)]
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

lemma g71y_cond_snoc {L : ℕ} (x y : ℕ) (A : ℕ → Prop) (ω : Fin (L + 1) → ℕ) :
    ((Fin.snoc ω y : Fin (L + 2) → ℕ) 0 = x ∧ (Fin.snoc ω y : Fin (L + 2) → ℕ) (Fin.last (L + 1)) = y ∧
      ∀ m : Fin (L + 2), m ≠ 0 → m ≠ Fin.last (L + 1) → A ((Fin.snoc ω y : Fin (L + 2) → ℕ) m)) ↔
    ((L = 0 ∨ A (ω (Fin.last L))) ∧ (ω 0 = x ∧ ω (Fin.last L) = ω (Fin.last L) ∧
      ∀ m : Fin (L + 1), m ≠ 0 → m ≠ Fin.last L → A (ω m))) := by
  have hz : (Fin.snoc ω y : Fin (L + 2) → ℕ) 0 = ω 0 := by
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

lemma g71y_PS_snoc (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) (x L y : ℕ) (A : ℕ → Prop)
    [DecidablePred A] :
    g71y_PS P x (L + 1) y A =
      ∑' z, (if L = 0 ∨ A z then g71y_PS P x L z A else 0) * ENNReal.ofReal (P z y) := by
  classical
  unfold g71y_PS
  rw [g71y_tsum_snoc]
  simp_rw [g71y_ite_tsum, ← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  rw [tsum_eq_single y, tsum_eq_single (ω (Fin.last L))]
  · have hcc := g71y_cond_snoc x y A ω
    rw [g71y_pw_snoc, ENNReal.ofReal_mul (g71y_pw_nonneg P h0 ω)]
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

lemma g71y_PS_one (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) (x y : ℕ) (A : ℕ → Prop) :
    g71y_PS P x 1 y A = ENNReal.ofReal (P x y) := by
  classical
  rw [g71y_PS_cons P h0, tsum_eq_single y]
  · simp [g71y_PS_zero]
  · intro z hz; simp [g71y_PS_zero, hz]

open Classical in
noncomputable def g71y_T (P : ℕ → ℕ → ℝ) (x L : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (L + 1) → ℕ, if ω 0 = x then ENNReal.ofReal (pathWeightC P ω) else 0

lemma g71y_T_one (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (x L : ℕ) : g71y_T P x L = 1 := by
  classical
  have h0 := hP.stochastic.1
  induction L with
  | zero =>
    unfold g71y_T
    rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    rw [tsum_eq_single x]
    · simp [pathWeightC]
    · intro b hb; simp [hb]
  | succ L ih =>
    rw [← ih]
    unfold g71y_T
    rw [g71y_tsum_snoc]
    refine tsum_congr fun ω => ?_
    have hz : ∀ k, (Fin.snoc ω k : Fin (L + 2) → ℕ) 0 = ω 0 := fun k => by
      have : (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc := rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [hz, g71y_pw_snoc]
    split_ifs
    · simp_rw [ENNReal.ofReal_mul (g71y_pw_nonneg P h0 ω)]
      rw [ENNReal.tsum_mul_left, g71y_rowsum P hP, mul_one]
    · simp

lemma g71y_PS_le (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (x L y : ℕ) (A : ℕ → Prop) :
    g71y_PS P x L y A ≤ 1 := by
  rw [← g71y_T_one P hP x L]
  unfold g71y_PS g71y_T
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs with h1 h2 <;> simp_all

lemma g71y_conv4 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    ∀ L x, m + 1 ≤ x → g71y_PS P x (L + 1) m (fun s => m < s) =
      (if L = 0 then ENNReal.ofReal (P x m) else 0) +
      ∑ s ∈ Finset.range L, g71y_PS P x (s + 1) (m + 1) (fun s => m + 1 < s) *
        g71y_PS P (m + 1) (L - s) m (fun s => m < s) := by
  classical
  have h0 := hP.stochastic.1
  intro L
  induction L with
  | zero => intro x _; rw [g71y_PS_one P h0]; simp
  | succ L ih =>
    intro x hx
    rw [g71y_PS_cons P h0 x (L + 1)]
    have key : ∀ z, ENNReal.ofReal (P x z) *
        (if L + 1 = 0 ∨ m < z then g71y_PS P z (L + 1) m (fun s => m < s) else 0) =
        (if z = m + 1 then ENNReal.ofReal (P x (m + 1)) *
          g71y_PS P (m + 1) (L + 1) m (fun s => m < s) else 0) +
        ∑ s ∈ Finset.range L, ENNReal.ofReal (P x z) *
          (if s + 1 = 0 ∨ m + 1 < z then g71y_PS P z (s + 1) (m + 1) (fun s => m + 1 < s) else 0) *
          g71y_PS P (m + 1) (L - s) m (fun s => m < s) := by
      intro z
      rcases lt_trichotomy z (m + 1) with hz | hz | hz
      · rw [if_neg (by omega), if_neg (by omega), mul_zero, zero_add]
        symm; apply Finset.sum_eq_zero; intro s _
        rw [if_neg (by omega), mul_zero, zero_mul]
      · subst hz
        rw [if_pos (Or.inr (by omega)), if_pos rfl]
        rw [Finset.sum_eq_zero (fun s _ => by rw [if_neg (by omega), mul_zero, zero_mul]), add_zero]
      · rw [if_pos (Or.inr (by omega)), if_neg (by omega), zero_add, ih z (by omega),
          hP.skipFree z m (Or.inr (by omega)), ENNReal.ofReal_zero, ite_self, zero_add,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos (Or.inr hz), mul_assoc]
    simp_rw [key]
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), tsum_ite_eq]
    simp_rw [ENNReal.tsum_mul_right]
    rw [if_neg (by omega), zero_add, Finset.sum_range_succ', g71y_PS_one P h0, Nat.sub_zero,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [g71y_PS_cons P h0 x (s + 1), show L + 1 - (s + 1) = L - s by omega]

lemma g71y_conv5 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    ∀ L y, m + 1 ≤ y → g71y_PS P m (L + 1) y (fun s => m < s) =
      (if L = 0 then ENNReal.ofReal (P m y) else 0) +
      ∑ s ∈ Finset.range L, g71y_PS P m (L - s) (m + 1) (fun s => m < s) *
        g71y_PS P (m + 1) (s + 1) y (fun s => m + 1 < s) := by
  classical
  have h0 := hP.stochastic.1
  intro L
  induction L with
  | zero => intro y _; rw [g71y_PS_one P h0]; simp
  | succ L ih =>
    intro y hy
    rw [g71y_PS_snoc P h0 m (L + 1)]
    have key : ∀ z,
        (if L + 1 = 0 ∨ m < z then g71y_PS P m (L + 1) z (fun s => m < s) else 0) *
          ENNReal.ofReal (P z y) =
        (if z = m + 1 then g71y_PS P m (L + 1) (m + 1) (fun s => m < s) *
          ENNReal.ofReal (P (m + 1) y) else 0) +
        ∑ s ∈ Finset.range L, g71y_PS P m (L - s) (m + 1) (fun s => m < s) *
          ((if s + 1 = 0 ∨ m + 1 < z then g71y_PS P (m + 1) (s + 1) z (fun s => m + 1 < s) else 0) *
          ENNReal.ofReal (P z y)) := by
      intro z
      rcases lt_trichotomy z (m + 1) with hz | hz | hz
      · rw [if_neg (by omega), if_neg (by omega), zero_mul, zero_add]
        symm; apply Finset.sum_eq_zero; intro s _
        rw [if_neg (by omega), zero_mul, mul_zero]
      · subst hz
        rw [if_pos (Or.inr (by omega)), if_pos rfl]
        rw [Finset.sum_eq_zero (fun s _ => by rw [if_neg (by omega), zero_mul, mul_zero]), add_zero]
      · rw [if_pos (Or.inr (by omega)), if_neg (by omega), zero_add, ih z (by omega),
          hP.skipFree m z (Or.inl (by omega)), ENNReal.ofReal_zero, ite_self, zero_add,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos (Or.inr hz), mul_assoc]
    simp_rw [key]
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), tsum_ite_eq]
    simp_rw [ENNReal.tsum_mul_left]
    rw [if_neg (by omega), zero_add, Finset.sum_range_succ', g71y_PS_one P h0, Nat.sub_zero,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [g71y_PS_snoc P h0 (m + 1) (s + 1), show L + 1 - (s + 1) = L - s by omega]

lemma g71y_id1 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (n k : ℕ) :
    g71y_PS P n (k + 2) n (fun s => n < s) =
      ENNReal.ofReal (P n (n + 1)) * g71y_PS P (n + 1) (k + 1) n (fun s => n < s) := by
  classical
  rw [g71y_PS_cons P hP.stochastic.1, tsum_eq_single (n + 1)]
  · rw [if_pos (Or.inr (by omega))]
  · intro z hz
    by_cases h : n < z
    · rw [hP.skipFree n z (Or.inl (by omega)), ENNReal.ofReal_zero, zero_mul]
    · rw [if_neg (by omega), mul_zero]

lemma g71y_id2 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (n k : ℕ) :
    g71y_PS P n (k + 2) n (fun s => n < s) =
      g71y_PS P n (k + 1) (n + 1) (fun s => n < s) * ENNReal.ofReal (P (n + 1) n) := by
  classical
  rw [g71y_PS_snoc P hP.stochastic.1, tsum_eq_single (n + 1)]
  · rw [if_pos (Or.inr (by omega))]
  · intro z hz
    by_cases h : n < z
    · rw [hP.skipFree z n (Or.inr (by omega)), ENNReal.ofReal_zero, mul_zero]
    · rw [if_neg (by omega), zero_mul]

lemma g71y_tri_le (f h : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * h p.2 ≤
      (∑ a ∈ Finset.range N, f a) * ∑ b ∈ Finset.range N, h b := by
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => f a * h b)]
  rw [Finset.range_eq_Ico, Finset.sum_mul]
  have := Finset.sum_Ico_Ico_comm 0 N (fun a n => f a * h (n - a))
  simp only [Nat.succ_eq_add_one] at this ⊢
  simp only [← Finset.range_eq_Ico] at this ⊢
  rw [← this]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum]
  gcongr
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le _ _))

section Hom
variable {b₀ a₀ a₁ a₂ : ℝ}

lemma g71y_hom_bd (h : IsHomParams b₀ a₀ a₁ a₂) : IsBirthDeath (homP b₀ a₀ a₁ a₂) := by
  have ha0 := h.a₀_pos; have ha1 := h.a₁_nonneg; have ha2 := h.a₂_pos
  have hr0 := h.row_zero; have hrs := h.row_sum
  refine ⟨⟨fun x y => ?_, fun x => ?_⟩, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · unfold homP; split_ifs <;> linarith
  · have hz : ∀ j ∉ Finset.range (x + 2), homP b₀ a₀ a₁ a₂ x j = 0 := by
      intro j hj; rw [Finset.mem_range, not_lt] at hj; unfold homP
      split_ifs <;> first | rfl | (exfalso; omega)
    have hs : ∑ j ∈ Finset.range (x + 2), homP b₀ a₀ a₁ a₂ x j = 1 := by
      rcases x with _ | x
      · simp [Finset.sum_range_succ, homP]; linarith
      · rw [show x + 1 + 2 = x + 3 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
            rw [Finset.mem_range] at hj; unfold homP
            split_ifs <;> first | rfl | (exfalso; omega))]
        simp [homP]; linarith
    exact hs ▸ hasSum_sum_of_ne_finset_zero hz
  · unfold homP; split_ifs <;> first | rfl | (exfalso; omega)
  · unfold homP; split_ifs <;> first | linarith | (exfalso; omega)
  · unfold homP; split_ifs <;> first | linarith | (exfalso; omega)


lemma g71y_homP_shift (x w : ℕ) (hx : 1 ≤ x ∨ 1 ≤ w) (hne : ¬ (x = 0 ∧ w = 0)) :
    homP b₀ a₀ a₁ a₂ (x + 1) (w + 1) = homP b₀ a₀ a₁ a₂ x w := by
  unfold homP; split_ifs <;> first | rfl | (exfalso; omega)

lemma g71y_shift (h : IsHomParams b₀ a₀ a₁ a₂) (n : ℕ) : ∀ L x y, (1 ≤ x ∨ 1 ≤ y) →
    g71y_PS (homP b₀ a₀ a₁ a₂) (x + 1) L (y + 1) (fun s => n + 1 < s) =
      g71y_PS (homP b₀ a₀ a₁ a₂) x L y (fun s => n < s) := by
  have h0 := (g71y_hom_bd h).stochastic.1
  intro L
  induction L with
  | zero => intro x y _; rw [g71y_PS_zero, g71y_PS_zero]; simp
  | succ L ih =>
    intro x y hxy
    rw [g71y_PS_cons _ h0 (x + 1), g71y_PS_cons _ h0 x, tsum_eq_zero_add' ENNReal.summable]
    have hz0 : ENNReal.ofReal (homP b₀ a₀ a₁ a₂ (x + 1) 0) *
        (if L = 0 ∨ n + 1 < 0 then g71y_PS (homP b₀ a₀ a₁ a₂) 0 L (y + 1) (fun s => n + 1 < s)
          else 0) = 0 := by
      by_cases hL : L = 0
      · subst hL; rw [if_pos (Or.inl rfl), g71y_PS_zero, if_neg (by omega), mul_zero]
      · rw [if_neg (by omega), mul_zero]
    rw [hz0, zero_add]
    refine tsum_congr fun w => ?_
    by_cases hc : L = 0 ∨ n < w
    · rw [if_pos (by omega), if_pos hc]
      by_cases hxw : x = 0 ∧ w = 0
      · obtain ⟨rfl, rfl⟩ := hxw
        have hL : L = 0 := by omega
        subst hL
        rw [g71y_PS_zero, g71y_PS_zero, if_neg (by omega), if_neg (by omega), mul_zero, mul_zero]
      · rw [g71y_homP_shift x w (by omega) hxw]
        congr 1
        rcases hc with hL | hnw
        · subst hL; rw [g71y_PS_zero, g71y_PS_zero]; simp
        · exact ih w y (Or.inl (by omega))
    · rw [if_neg (by omega), if_neg hc, mul_zero, mul_zero]

lemma g71y_glevel (h : IsHomParams b₀ a₀ a₁ a₂) (k : ℕ) : ∀ m,
    g71y_PS (homP b₀ a₀ a₁ a₂) (m + 1) k m (fun s => m < s) =
      g71y_PS (homP b₀ a₀ a₁ a₂) 1 k 0 (fun s => 0 < s) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [g71y_shift h m k (m + 1) m (Or.inl (by omega)), ih]

lemma g71y_rlevel (h : IsHomParams b₀ a₀ a₁ a₂) (k : ℕ) : ∀ m,
    g71y_PS (homP b₀ a₀ a₁ a₂) m k (m + 1) (fun s => m < s) =
      g71y_PS (homP b₀ a₀ a₁ a₂) 0 k 1 (fun s => 0 < s) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [g71y_shift h m k m (m + 1) (Or.inr (by omega)), ih]

theorem solution (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂) (n : ℕ) (hn : 1 ≤ n) :
    Gz (homP b₀ a₀ a₁ a₂) n 1 = ((min 1 (a₂ / a₀) : ℝ) : ℂ) ∧
    Rz (homP b₀ a₀ a₁ a₂) n 1 = ((min 1 (a₀ / a₂) : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hP := g71y_hom_bd h
  have h0 := hP.stochastic.1
  have ha0 := h.a₀_pos; have ha1 := h.a₁_nonneg; have ha2 := h.a₂_pos; have hrs := h.row_sum
  set P := homP b₀ a₀ a₁ a₂ with hPdef
  have hle := g71y_PS_le P hP
  set gc : ℕ → ℝ≥0∞ := fun k => g71y_PS P 1 k 0 (fun s => 0 < s) with hgc
  set uc : ℕ → ℝ≥0∞ := fun k => g71y_PS P 1 k 1 (fun s => 1 < s) with huc
  set rc : ℕ → ℝ≥0∞ := fun k => g71y_PS P 0 k 1 (fun s => 0 < s) with hrc
  have P11 : P 1 1 = a₁ := by simp [hPdef, homP]
  have P10 : P 1 0 = a₂ := by simp [hPdef, homP]
  have P12 : P 1 2 = a₀ := by simp [hPdef, homP]
  have P21 : P 2 1 = a₂ := by simp [hPdef, homP]
  set G := ∑' k, gc (k + 1) with hG
  set U := ∑' k, uc (k + 1) with hU
  set R := ∑' k, rc (k + 1) with hR
  have E1 : U = ENNReal.ofReal a₁ + ENNReal.ofReal a₀ * G := by
    rw [hU, tsum_eq_zero_add' ENNReal.summable, hG, ← ENNReal.tsum_mul_left]
    simp only [huc, zero_add]
    rw [g71y_PS_one P h0, P11]
    congr 1
    refine tsum_congr fun k => ?_
    rw [g71y_id1 P hP 1 k, P12, g71y_shift h 0 (k + 1) 1 0 (Or.inl le_rfl)]
  have E2 : U = ENNReal.ofReal a₁ + R * ENNReal.ofReal a₂ := by
    rw [hU, tsum_eq_zero_add' ENNReal.summable, hR, ← ENNReal.tsum_mul_right]
    simp only [huc, zero_add]
    rw [g71y_PS_one P h0, P11]
    congr 1
    refine tsum_congr fun k => ?_
    rw [g71y_id2 P hP 1 k, P21, g71y_shift h 0 (k + 1) 0 1 (Or.inr le_rfl)]
  have hconv : ∀ k, gc (k + 2) = ∑ s ∈ Finset.range (k + 1), uc (s + 1) * gc (k - s + 1) := by
    intro k
    have := g71y_conv4 P hP 0 (k + 1) 1 le_rfl
    simp only [zero_add] at this
    rw [show k + 2 = k + 1 + 1 by ring]
    simp only [hgc, huc]
    rw [this, if_neg (by omega), zero_add]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show k + 1 - s = k - s + 1 by omega]
  have huc1 : uc 1 = ENNReal.ofReal a₁ := by rw [huc]; simp only; rw [g71y_PS_one P h0, P11]
  have huc2 : ∀ k, uc (k + 2) = ENNReal.ofReal a₀ * gc (k + 1) := by
    intro k; rw [huc, hgc]; simp only
    rw [g71y_id1 P hP 1 k, P12, g71y_shift h 0 (k + 1) 1 0 (Or.inl le_rfl)]
  have hgc1 : gc 1 = ENNReal.ofReal a₂ := by rw [hgc]; simp only; rw [g71y_PS_one P h0, P10]
  have hgE : ∀ k, gc k = g71y_gE P k := by
    intro k; rw [hgc]; simp only; unfold g71y_PS g71y_gE
    refine tsum_congr fun ω => ?_
    by_cases hc : (ω 0 = 1 ∧ ω (Fin.last k) = 0 ∧ ∀ m : Fin (k + 1), m ≠ 0 → m ≠ Fin.last k → 0 < ω m)
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
  have hG1 : G ≤ 1 := by
    refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
    have := g71y_mass P hP t
    simp_rw [hgE]
    rw [← this]; exact le_add_self
  have hGt : G ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hG1
  have hUt : U ≠ ⊤ := by
    rw [E1]; exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGt⟩
  have hnt : ∀ c : ℕ → ℝ≥0∞, (∀ k, c k ≤ 1) → ∀ k, c k ≠ ⊤ :=
    fun c hc k => ne_top_of_le_ne_top ENNReal.one_ne_top (hc k)
  have hgle : ∀ k, gc k ≤ 1 := fun k => hle _ _ _ _
  have hule : ∀ k, uc k ≤ 1 := fun k => hle _ _ _ _
  have hGr : G.toReal = ∑' k, (gc (k + 1)).toReal :=
    (ENNReal.tsum_toReal_eq (fun k => hnt gc hgle (k + 1)))
  have hUr : U.toReal = ∑' k, (uc (k + 1)).toReal :=
    (ENNReal.tsum_toReal_eq (fun k => hnt uc hule (k + 1)))
  have sg : Summable (fun k => (gc (k + 1)).toReal) := ENNReal.summable_toReal hGt
  have su : Summable (fun k => (uc (k + 1)).toReal) := ENNReal.summable_toReal hUt
  have ng : Summable (fun k => ‖(gc (k + 1)).toReal‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using sg
  have nu : Summable (fun k => ‖(uc (k + 1)).toReal‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using su
  have E4r : G.toReal = a₂ + U.toReal * G.toReal := by
    rw [hUr, hGr, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm nu ng, sg.tsum_eq_zero_add]
    simp only [zero_add]
    rw [hgc1, ENNReal.toReal_ofReal ha2.le]
    congr 1
    refine tsum_congr fun k => ?_
    rw [show k + 1 + 1 = k + 2 by ring, hconv k,
      ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (hnt uc hule _) (hnt gc hgle _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.toReal_mul]
  have E1r : U.toReal = a₁ + a₀ * G.toReal := by
    rw [E1, ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGt),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ha1, ENNReal.toReal_ofReal ha0.le]
  have Eq : ENNReal.ofReal a₀ * G = R * ENNReal.ofReal a₂ :=
    (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp (E1.symm.trans E2)
  have hRt : R ≠ ⊤ := by
    intro hR'
    rw [hR', ENNReal.top_mul (by simpa using ha2)] at Eq
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGt Eq
  have Er : a₀ * G.toReal = R.toReal * a₂ := by
    have := congrArg ENNReal.toReal Eq
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0.le,
      ENNReal.toReal_ofReal ha2.le] at this
  set g := G.toReal with hg
  have hq : (a₀ * g - a₂) * (g - 1) = 0 := by
    rw [E1r] at E4r
    linear_combination (-1 : ℝ) * E4r + (-g) * hrs
  have hg1 : g ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hG1)
  have hGz : Gz P (m + 1) 1 = ((g : ℝ) : ℂ) := by
    unfold Gz
    simp only [one_pow, one_mul]
    rw [← Complex.ofReal_tsum, hGr]
    congr 1
    refine tsum_congr fun k => ?_
    unfold MatrixAnalytic.BirthDeath.g
    rw [g71y_taboo_eq P h0]
    simp only [Nat.add_sub_cancel]
    rw [g71y_glevel h]
  have hRz : Rz P (m + 1) 1 = ((R.toReal : ℝ) : ℂ) := by
    unfold Rz
    simp only [one_pow, one_mul]
    rw [← Complex.ofReal_tsum, hR, (ENNReal.tsum_toReal_eq (fun k => hnt rc (fun k => hle _ _ _ _) (k + 1)))]
    congr 1
    refine tsum_congr fun k => ?_
    unfold MatrixAnalytic.BirthDeath.r
    rw [g71y_taboo_eq P h0]
    simp only [Nat.add_sub_cancel]
    rw [g71y_rlevel h]
  have hRr : R.toReal = a₀ * g / a₂ := by rw [Er]; field_simp
  rw [hGz, hRz, hRr]
  rcases lt_or_ge a₂ a₀ with hlt | hge
  · -- transient: minimality
    set x := a₂ / a₀ with hx
    have hx0 : 0 ≤ x := by positivity
    have hax : a₀ * x = a₂ := by rw [hx]; field_simp
    have hfix : a₂ + (a₁ + a₀ * x) * x = x := by linear_combination (x - 1) * hax + x * hrs
    have hfixE : (ENNReal.ofReal a₁ + ENNReal.ofReal a₀ * ENNReal.ofReal x) * ENNReal.ofReal x +
        ENNReal.ofReal a₂ = ENNReal.ofReal x := by
      rw [← ENNReal.ofReal_mul ha0.le, ← ENNReal.ofReal_add ha1 (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) ha2.le]
      congr 1; linarith
    have hUN : ∀ N, ∑ s ∈ Finset.range N, uc (s + 1) ≤
        ENNReal.ofReal a₁ + ENNReal.ofReal a₀ * ∑ j ∈ Finset.range N, gc (j + 1) := by
      intro N
      rcases N with _ | N
      · simp
      · rw [Finset.sum_range_succ', huc1, add_comm]
        simp_rw [huc2]
        rw [← Finset.mul_sum]
        gcongr
        first | omega | exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ N))
    have main : ∀ N, ∑ k ∈ Finset.range N, gc (k + 1) ≤ ENNReal.ofReal x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ', hgc1]
        have h1 : ∑ k ∈ Finset.range N, gc (k + 1 + 1) ≤
            (∑ a ∈ Finset.range N, uc (a + 1)) * ∑ b ∈ Finset.range N, gc (b + 1) := by
          have := g71y_tri_le (fun a => uc (a + 1)) (fun b => gc (b + 1)) N
          simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => uc (a + 1) * gc (b + 1))] at this
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) this
          rw [show k + 1 + 1 = k + 2 by ring, hconv k]
        calc ∑ k ∈ Finset.range N, gc (k + 1 + 1) + ENNReal.ofReal a₂
            ≤ (ENNReal.ofReal a₁ + ENNReal.ofReal a₀ * ENNReal.ofReal x) * ENNReal.ofReal x +
              ENNReal.ofReal a₂ := by
              gcongr
              refine h1.trans ?_
              gcongr
              exact (hUN N).trans (by gcongr)
          _ = ENNReal.ofReal x := hfixE
    have hGx : G ≤ ENNReal.ofReal x := ENNReal.tsum_le_of_sum_range_le main
    have hgx : g ≤ x := ENNReal.toReal_le_of_le_ofReal hx0 hGx
    have hx1 : x < 1 := by rw [hx, div_lt_one ha0]; exact hlt
    have hgeq : a₀ * g = a₂ := by
      have : g - 1 ≠ 0 := by linarith
      have := (mul_eq_zero.mp hq).resolve_right this
      linarith
    have hgv : g = x := by rw [hx]; field_simp; linarith
    rw [min_eq_right hx1.le, min_eq_left ((one_le_div ha2).mpr hlt.le), hgv, hax, div_self ha2.ne']
    simp [hx]
  · have hgv : g = 1 := by
      rcases mul_eq_zero.mp hq with h1 | h1
      · have : a₂ ≤ a₀ * g := by nlinarith
        nlinarith
      · linarith
    rw [hgv, min_eq_left ((one_le_div ha0).mpr hge), min_eq_right ((div_le_one ha2).mpr hge), mul_one]
    simp
