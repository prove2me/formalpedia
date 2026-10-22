-- Prove2me | solution 1 for MatrixAnalytic.BirthDeath.homogeneous_geometric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:42:10.144988+00:00
-- url     : https://prove2.me/submissions/ef83421a-dd6d-4dfd-8e89-935a8b3a3fff

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

lemma g71y_GR_at_one (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂) (n : ℕ) (hn : 1 ≤ n) :
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

end Hom

lemma g71y_SA_eq (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) (x t : ℕ) :
    setAvoidTailC P x {0} t = (g71y_SAE P x t).toReal := by
  unfold setAvoidTailC g71y_SAE
  rw [g71y_toReal_tsum _ (fun ω => by split_ifs; exacts [g71y_pw_nonneg P h0 ω, le_rfl])]
  congr 1
  refine tsum_congr fun ω => ?_
  simp only [Set.mem_singleton_iff]
  split_ifs <;> simp

lemma g71y_g_eq (P : ℕ → ℕ → ℝ) (h0 : ∀ x y, 0 ≤ P x y) (k : ℕ) :
    g P 1 k = (g71y_gE P k).toReal := by
  unfold g tabooProb g71y_gE
  rw [g71y_toReal_tsum _ (fun ω => by split_ifs; exacts [g71y_pw_nonneg P h0 ω, le_rfl])]
  congr 1
  refine tsum_congr fun ω => ?_
  split_ifs <;> simp

lemma g71y_R1 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (t : ℕ) :
    g71y_SAE P 0 (t + 1) = ENNReal.ofReal (P 0 1) * g71y_SAE P 1 t := by
  classical
  have h0 := hP.stochastic.1
  unfold g71y_SAE
  rw [g71y_tsum_cons, tsum_eq_single 0, ← ENNReal.tsum_mul_left]
  · refine tsum_congr fun ω => ?_
    have hc : ((Fin.cons 0 ω : Fin (t + 2) → ℕ) 0 = 0 ∧
        ∀ i : Fin (t + 2), i ≠ 0 → (Fin.cons 0 ω : Fin (t + 2) → ℕ) i ≠ 0) ↔
        ∀ j : Fin (t + 1), ω j ≠ 0 := by
      rw [Fin.forall_fin_succ]
      simp
    rw [if_congr hc rfl rfl, g71y_pw_cons]
    rcases Nat.lt_trichotomy (ω 0) 1 with h | h | h
    · have hz : ω 0 = 0 := by omega
      rw [if_neg (fun hh => hh 0 hz), if_neg (fun hh => by have := hh.1; omega), mul_zero]
    · have hc2 : (∀ j : Fin (t + 1), ω j ≠ 0) ↔ (ω 0 = 1 ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ 0) := by
        constructor
        · intro hh; exact ⟨h, fun i _ => hh i⟩
        · rintro ⟨-, hh⟩ j
          by_cases hj : j = 0
          · rw [hj, h]; omega
          · exact hh j hj
      rw [if_congr hc2 rfl rfl]
      split_ifs
      · rw [h, ENNReal.ofReal_mul (h0 _ _)]
      · simp
    · have hz : P 0 (ω 0) = 0 := hP.skipFree 0 (ω 0) (Or.inl (by omega))
      rw [hz, zero_mul, ENNReal.ofReal_zero, ite_self,
        if_neg (fun hh => by have := hh.1; omega), mul_zero]
  · intro k hk
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hk (by simpa using h)

lemma g71y_rec_iff (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    Recurrent P 0 ↔ G P 1 = 1 := by
  have h0 := hP.stochastic.1
  have hfin : ∀ t, g71y_SAE P 1 t ≠ ⊤ ∧ ∀ k ∈ Finset.range t, g71y_gE P (k + 1) ≠ ⊤ := by
    intro t
    have := g71y_mass P hP t
    refine ⟨fun h => by rw [h, top_add] at this; exact ENNReal.top_ne_one this, fun k hk h => ?_⟩
    have hle : g71y_gE P (k + 1) ≤ ∑ k ∈ Finset.range t, g71y_gE P (k + 1) :=
      Finset.single_le_sum (f := fun k => g71y_gE P (k + 1)) (fun _ _ => bot_le) hk
    have : ∑ k ∈ Finset.range t, g71y_gE P (k + 1) ≤ 1 := by
      rw [← this]; exact le_add_self
    rw [h] at hle
    exact ENNReal.one_ne_top (top_le_iff.mp (hle.trans this))
  have hR2 : ∀ t, setAvoidTailC P 1 {0} t + ∑ k ∈ Finset.range t, g P 1 (k + 1) = 1 := by
    intro t
    have := congrArg ENNReal.toReal (g71y_mass P hP t)
    rw [ENNReal.toReal_add (hfin t).1 (ENNReal.sum_ne_top.mpr (hfin t).2),
      ENNReal.toReal_sum (hfin t).2, ENNReal.toReal_one] at this
    rw [g71y_SA_eq P h0]
    simp_rw [g71y_g_eq P h0]
    exact this
  have hR1 : ∀ t, returnTailC P 0 (t + 1) = P 0 1 * setAvoidTailC P 1 {0} t := by
    intro t
    unfold returnTailC
    rw [g71y_SA_eq P h0, g71y_SA_eq P h0, g71y_R1 P hP, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (h0 0 1)]
  have hgnn : ∀ k, 0 ≤ g P 1 k := fun k => by rw [g71y_g_eq P h0]; exact ENNReal.toReal_nonneg
  have hSAnn : ∀ t, 0 ≤ setAvoidTailC P 1 {0} t := fun t => by
    rw [g71y_SA_eq P h0]; exact ENNReal.toReal_nonneg
  have hsum : Summable (fun k => g P 1 (k + 1)) :=
    summable_of_sum_range_le (fun k => hgnn _) (fun t => by
      have h1 := hR2 t; have h2 := hSAnn t
      show ∑ k ∈ Finset.range t, g P 1 (k + 1) ≤ 1
      linarith)
  have hlim : Filter.Tendsto (fun t => ∑ k ∈ Finset.range t, g P 1 (k + 1)) Filter.atTop
      (nhds (G P 1)) := hsum.hasSum.tendsto_sum_nat
  have hlim2 : Filter.Tendsto (fun t => returnTailC P 0 (t + 1)) Filter.atTop
      (nhds (P 0 1 * (1 - G P 1))) := by
    have : (fun t => returnTailC P 0 (t + 1)) =
        fun t => P 0 1 * (1 - ∑ k ∈ Finset.range t, g P 1 (k + 1)) := by
      funext t; rw [hR1]; congr 1; linarith [hR2 t]
    rw [this]
    exact (tendsto_const_nhds.sub hlim).const_mul _
  have hp := hP.up_pos 0
  unfold Recurrent
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  constructor
  · intro h
    have := tendsto_nhds_unique hlim2 h
    have : 1 - G P 1 = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hp.ne'
      · exact h'
    linarith
  · intro h
    rw [h, sub_self, mul_zero] at hlim2
    exact hlim2

/-! ### g77c: first-passage / last-exit library for birth-and-death chains -/

lemma g77c_shift (b : ℕ → ℝ≥0∞) (s : ℕ) :
    ∑' L, (if s < L then b (L - s) else 0) = ∑' j, b (j + 1) := by
  induction s with
  | zero =>
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp
  | succ s ih =>
    rw [tsum_eq_zero_add' ENNReal.summable, if_neg (by omega), zero_add, ← ih]
    refine tsum_congr fun L => ?_
    by_cases h : s < L
    · rw [if_pos (by omega), if_pos h]; congr 1; omega
    · rw [if_neg (by omega), if_neg h]

lemma g77c_cauchy (a b : ℕ → ℝ≥0∞) :
    ∑' L, ∑ s ∈ Finset.range L, a s * b (L - s) = (∑' i, a i) * ∑' j, b (j + 1) := by
  have e : ∀ L, ∑ s ∈ Finset.range L, a s * b (L - s) =
      ∑' s, a s * (if s < L then b (L - s) else 0) := by
    intro L
    rw [tsum_eq_sum (s := Finset.range L)]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [if_pos (Finset.mem_range.mp hs)]
    · intro s hs; rw [if_neg (by simpa using hs), mul_zero]
  simp_rw [e]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun s => ?_
  rw [ENNReal.tsum_mul_left, g77c_shift]

noncomputable def g77c_QE (P : ℕ → ℕ → ℝ) (m x t : ℕ) : ℝ≥0∞ :=
  ∑' z, if m < z then g71y_PS P x t z (fun s => m < s) else 0

lemma g77c_rowsum_ge (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m w : ℕ) (hw : m < w) :
    ∑' z, (if m < z then ENNReal.ofReal (P w z) else 0) + ENNReal.ofReal (P w m) = 1 := by
  rw [← g71y_rowsum P hP w]
  have : ∀ z, ENNReal.ofReal (P w z) = (if m < z then ENNReal.ofReal (P w z) else 0) +
      (if z = m then ENNReal.ofReal (P w m) else 0) := by
    intro z
    rcases lt_trichotomy m z with h | h | h
    · rw [if_pos h, if_neg (by omega), add_zero]
    · subst h; rw [if_neg (lt_irrefl _), if_pos rfl, zero_add]
    · rw [if_neg (by omega), if_neg (by omega), zero_add,
        hP.skipFree w z (Or.inr (by omega)), ENNReal.ofReal_zero]
  conv_rhs => rw [tsum_congr this]
  rw [ENNReal.tsum_add, tsum_ite_eq]

lemma g77c_Qstep (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m x t : ℕ) (hx : m < x) :
    g77c_QE P m x (t + 1) + g71y_PS P x (t + 1) m (fun s => m < s) = g77c_QE P m x t := by
  classical
  have h0 := hP.stochastic.1
  unfold g77c_QE
  have e1 : ∀ z, (if m < z then g71y_PS P x (t + 1) z (fun s => m < s) else 0) =
      ∑' w, (if t = 0 ∨ m < w then g71y_PS P x t w (fun s => m < s) else 0) *
        (if m < z then ENNReal.ofReal (P w z) else 0) := by
    intro z
    by_cases hz : m < z
    · simp only [if_pos hz]; rw [g71y_PS_snoc P h0]
    · simp only [if_neg hz, mul_zero, tsum_zero]
  simp_rw [e1]
  rw [ENNReal.tsum_comm, g71y_PS_snoc P h0]
  simp_rw [ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun w => ?_
  rw [← mul_add]
  by_cases hw : m < w
  · rw [g77c_rowsum_ge P hP m w hw, mul_one, if_pos (Or.inr hw), if_pos hw]
  · rw [if_neg hw]
    by_cases ht : t = 0
    · subst ht
      rw [if_pos (Or.inl rfl), g71y_PS_zero, if_neg (by omega), zero_mul]
    · rw [if_neg (by tauto), zero_mul]

lemma g77c_mass (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m x : ℕ) (hx : m < x) (t : ℕ) :
    g77c_QE P m x t + ∑ k ∈ Finset.range t, g71y_PS P x (k + 1) m (fun s => m < s) = 1 := by
  classical
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    unfold g77c_QE
    rw [tsum_eq_single x]
    · rw [if_pos hx, g71y_PS_zero, if_pos rfl]
    · intro z hz; rw [g71y_PS_zero, if_neg (Ne.symm hz)]; simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (g71y_PS P x (t + 1) m _), ← add_assoc,
      add_comm (g71y_PS P x (t + 1) m _), g77c_Qstep P hP m x t hx, ih]

lemma g77c_fp_le (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m x : ℕ) (hx : m < x) :
    ∑' k, g71y_PS P x (k + 1) m (fun s => m < s) ≤ 1 := by
  refine ENNReal.tsum_le_of_sum_range_le fun t => ?_
  rw [← g77c_mass P hP m x hx t]; exact le_add_self

noncomputable def g77c_GE (P : ℕ → ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∑' k, g71y_PS P (m + 1) (k + 1) m (fun s => m < s)
noncomputable def g77c_UE (P : ℕ → ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∑' k, g71y_PS P m (k + 1) m (fun s => m < s)
noncomputable def g77c_RE (P : ℕ → ℕ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∑' k, g71y_PS P m (k + 1) (m + 1) (fun s => m < s)

lemma g77c_E1 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    g77c_UE P m = ENNReal.ofReal (P m m) + ENNReal.ofReal (P m (m + 1)) * g77c_GE P m := by
  unfold g77c_UE g77c_GE
  rw [tsum_eq_zero_add' ENNReal.summable, g71y_PS_one P hP.stochastic.1, ← ENNReal.tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  exact g71y_id1 P hP m k

lemma g77c_E2 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    g77c_UE P m = ENNReal.ofReal (P m m) + g77c_RE P m * ENNReal.ofReal (P (m + 1) m) := by
  unfold g77c_UE g77c_RE
  rw [tsum_eq_zero_add' ENNReal.summable, g71y_PS_one P hP.stochastic.1, ← ENNReal.tsum_mul_right]
  congr 1
  refine tsum_congr fun k => ?_
  exact g71y_id2 P hP m k

lemma g77c_E3 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    g77c_GE P m = ENNReal.ofReal (P (m + 1) m) + g77c_UE P (m + 1) * g77c_GE P m := by
  have e : ∀ L, g71y_PS P (m + 1) (L + 1) m (fun s => m < s) =
      (if L = 0 then ENNReal.ofReal (P (m + 1) m) else 0) +
      ∑ s ∈ Finset.range L, g71y_PS P (m + 1) (s + 1) (m + 1) (fun s => m + 1 < s) *
        g71y_PS P (m + 1) (L - s) m (fun s => m < s) := fun L => g71y_conv4 P hP m L (m + 1) le_rfl
  have hc := g77c_cauchy (fun s => g71y_PS P (m + 1) (s + 1) (m + 1) (fun s => m + 1 < s))
    (fun j => g71y_PS P (m + 1) j m (fun s => m < s))
  conv_lhs => unfold g77c_GE; rw [tsum_congr e]
  rw [ENNReal.tsum_add, tsum_ite_eq, hc]
  rfl

lemma g77c_GE_le (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) : g77c_GE P m ≤ 1 :=
  g77c_fp_le P hP m (m + 1) (by omega)

lemma g77c_GR (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    ENNReal.ofReal (P m (m + 1)) * g77c_GE P m = g77c_RE P m * ENNReal.ofReal (P (m + 1) m) :=
  (ENNReal.add_right_inj ENNReal.ofReal_ne_top).mp ((g77c_E1 P hP m).symm.trans (g77c_E2 P hP m))

lemma g77c_GE_ne_top (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) : g77c_GE P m ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (g77c_GE_le P hP m)

lemma g77c_RE_ne_top (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) : g77c_RE P m ≠ ⊤ := by
  intro h
  have e := g77c_GR P hP m
  rw [h, ENNReal.top_mul (by simpa using hP.down_pos m)] at e
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g77c_GE_ne_top P hP m) e

lemma g77c_UE_ne_top (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) : g77c_UE P m ≠ ⊤ := by
  rw [g77c_E1 P hP m]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g77c_GE_ne_top P hP m)⟩

lemma g77c_G_eq (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    G P (m + 1) = (g77c_GE P m).toReal := by
  unfold G g g77c_GE
  rw [ENNReal.tsum_toReal_eq (fun k => ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _))]
  refine tsum_congr fun k => ?_
  simp only [Nat.add_sub_cancel]
  exact g71y_taboo_eq P hP.stochastic.1 _ _ _ _

lemma g77c_R_eq (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    R P (m + 1) = (g77c_RE P m).toReal := by
  unfold R r g77c_RE
  rw [ENNReal.tsum_toReal_eq (fun k => ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _))]
  refine tsum_congr fun k => ?_
  simp only [Nat.add_sub_cancel]
  exact g71y_taboo_eq P hP.stochastic.1 _ _ _ _

lemma g77c_U_eq (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    U P m = (g77c_UE P m).toReal := by
  unfold U u g77c_UE
  rw [ENNReal.tsum_toReal_eq (fun k => ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _))]
  refine tsum_congr fun k => ?_
  exact g71y_taboo_eq P hP.stochastic.1 _ _ _ _

lemma g77c_rowfin (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (y : ℕ) :
    ∑ x ∈ Finset.range (y + 2), P y x = 1 := by
  have h1 := hP.stochastic.2 y
  have h2 : HasSum (P y) (∑ x ∈ Finset.range (y + 2), P y x) := by
    refine hasSum_sum_of_ne_finset_zero fun x hx => ?_
    rw [Finset.mem_range, not_lt] at hx
    exact hP.skipFree y x (Or.inl (by omega))
  exact h2.unique h1

lemma g77c_row0 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) : P 0 0 + P 0 1 = 1 := by
  have := g77c_rowfin P hP 0
  simpa [Finset.sum_range_succ] using this

lemma g77c_row3 (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    P (m + 1) m + P (m + 1) (m + 1) + P (m + 1) (m + 2) = 1 := by
  have := g77c_rowfin P hP (m + 1)
  rw [show m + 1 + 2 = m + 3 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_eq_zero (fun x hx => by
      rw [Finset.mem_range] at hx; exact hP.skipFree (m + 1) x (Or.inr (by omega)))] at this
  rw [← this]; ring

/-- Real relations. -/
lemma g77c_rel (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    P m (m + 1) * G P (m + 1) = R P (m + 1) * P (m + 1) m ∧
    G P (m + 1) = P (m + 1) m + (P (m + 1) (m + 1) + P (m + 1) (m + 2) * G P (m + 2)) * G P (m + 1)
    ∧ 0 ≤ G P (m + 1) ∧ G P (m + 1) ≤ 1 ∧ 0 ≤ R P (m + 1) := by
  have h0 := hP.stochastic.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg ENNReal.toReal (g77c_GR P hP m)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 _ _),
      ENNReal.toReal_ofReal (h0 _ _), ← g77c_G_eq P hP, ← g77c_R_eq P hP] at this
  · have e3 := congrArg ENNReal.toReal (g77c_E3 P hP m)
    rw [g77c_E1 P hP (m + 1)] at e3
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (by
        rw [← g77c_E1 P hP (m + 1)]; exact g77c_UE_ne_top P hP _) (g77c_GE_ne_top P hP m)),
      ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g77c_GE_ne_top P hP _)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 _ _), ENNReal.toReal_ofReal (h0 _ _),
      ENNReal.toReal_ofReal (h0 _ _), ← g77c_G_eq P hP, ← g77c_G_eq P hP] at e3
    exact e3
  · rw [g77c_G_eq P hP]; exact ENNReal.toReal_nonneg
  · rw [g77c_G_eq P hP]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using g77c_GE_le P hP m)
  · rw [g77c_R_eq P hP]; exact ENNReal.toReal_nonneg

lemma g77c_lastexit (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (A : ℕ → Prop) (n x : ℕ)
    (hA : ∀ s, n ≤ s → A s) (hx : x ≤ n) :
    ∀ L y, n + 1 ≤ y → g71y_PS P x (L + 1) y A =
      ∑ s ∈ Finset.range (L + 1), g71y_PS P x s n A * g71y_PS P n (L + 1 - s) y (fun s => n < s) := by
  classical
  have h0 := hP.stochastic.1
  intro L
  induction L with
  | zero =>
    intro y hy
    rw [g71y_PS_one P h0, Finset.sum_range_one, g71y_PS_zero, g71y_PS_one P h0]
    by_cases hxn : x = n
    · subst hxn; simp
    · rw [if_neg hxn, zero_mul, hP.skipFree x y (Or.inl (by omega)), ENNReal.ofReal_zero]
  | succ L ih =>
    intro y hy
    rw [g71y_PS_snoc P h0 x (L + 1)]
    have key : ∀ z, (if L + 1 = 0 ∨ A z then g71y_PS P x (L + 1) z A else 0) *
        ENNReal.ofReal (P z y) =
        (if z = n then g71y_PS P x (L + 1) n A * ENNReal.ofReal (P n y) else 0) +
        ∑ s ∈ Finset.range (L + 1), g71y_PS P x s n A *
          ((if L + 1 - s = 0 ∨ n < z then g71y_PS P n (L + 1 - s) z (fun s => n < s) else 0) *
            ENNReal.ofReal (P z y)) := by
      intro z
      rcases lt_trichotomy z n with hz | hz | hz
      · rw [hP.skipFree z y (Or.inl (by omega)), ENNReal.ofReal_zero]
        simp only [mul_zero, Finset.sum_const_zero, add_zero]
        rw [if_neg (by omega)]
      · subst hz
        rw [if_pos (Or.inr (hA z le_rfl)), if_pos rfl]
        rw [Finset.sum_eq_zero (fun s hs => by
          rw [Finset.mem_range] at hs
          rw [if_neg (by omega), zero_mul, mul_zero]), add_zero]
      · rw [if_pos (Or.inr (hA z hz.le)), if_neg (by omega), zero_add, ih z (by omega),
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos (Or.inr hz), mul_assoc]
    simp_rw [key]
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), tsum_ite_eq]
    simp_rw [ENNReal.tsum_mul_left]
    rw [Finset.sum_range_succ _ (L + 1), show L + 1 + 1 - (L + 1) = 1 by omega, g71y_PS_one P h0, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [show L + 1 + 1 - s = (L + 1 - s) + 1 by omega, g71y_PS_snoc P h0 n (L + 1 - s)]

noncomputable def g77c_VE (P : ℕ → ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑' t, g71y_PS P 0 (t + 1) n (fun s => 0 < s)

lemma g77c_VE_succ (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (n : ℕ) (hn : 1 ≤ n) :
    g77c_VE P (n + 1) = g77c_VE P n * g77c_RE P n := by
  set a : ℕ → ℝ≥0∞ := fun s => g71y_PS P 0 s n (fun s => 0 < s) with ha
  set b : ℕ → ℝ≥0∞ := fun j => g71y_PS P n j (n + 1) (fun s => n < s) with hb
  have e : ∀ L, g71y_PS P 0 (L + 1) (n + 1) (fun s => 0 < s) =
      ∑ s ∈ Finset.range (L + 1), a s * b (L + 1 - s) :=
    fun L => g77c_lastexit P hP _ n 0 (fun s hs => by omega) (by omega) L (n + 1) le_rfl
  have hc := g77c_cauchy a b
  have h2 : ∑' L, ∑ s ∈ Finset.range L, a s * b (L - s) =
      ∑' L, ∑ s ∈ Finset.range (L + 1), a s * b (L + 1 - s) := by
    rw [tsum_eq_zero_add' ENNReal.summable]; simp
  unfold g77c_VE
  rw [tsum_congr e, ← h2, hc, tsum_eq_zero_add' ENNReal.summable]
  simp only [ha, g71y_PS_zero, if_neg (show (0:ℕ) ≠ n by omega), zero_add]
  rfl

lemma g77c_VE_prod (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (k : ℕ) :
    g77c_VE P (k + 1) = ∏ i ∈ Finset.range (k + 1), g77c_RE P i := by
  induction k with
  | zero => rw [Finset.prod_range_one]; rfl
  | succ k ih => rw [g77c_VE_succ P hP (k + 1) (by omega), ih, Finset.prod_range_succ _ (k + 1)]

lemma g77c_SAE_zero (P : ℕ → ℕ → ℝ) : g71y_SAE P 0 0 = 1 := by
  classical
  unfold g71y_SAE
  rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  rw [tsum_eq_single 0]
  · simp [pathWeightC]
  · intro b hb; simp [hb]

lemma g77c_SAE_le (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (x t : ℕ) : g71y_SAE P x t ≤ 1 := by
  rw [← g71y_T_one P hP x t]
  unfold g71y_SAE g71y_T
  refine ENNReal.tsum_le_tsum fun ω => ?_
  split_ifs <;> simp_all

lemma g77c_SAE_succ (P : ℕ → ℕ → ℝ) (t : ℕ) :
    g71y_SAE P 0 (t + 1) = ∑' n, g71y_PS P 0 (t + 1) (n + 1) (fun s => 0 < s) := by
  classical
  unfold g71y_SAE g71y_PS
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ω => ?_
  by_cases hl : ω (Fin.last (t + 1)) = 0
  · rw [if_neg (fun hc => hc.2 _ (by simp [Fin.ext_iff]) hl)]
    symm; apply ENNReal.tsum_eq_zero.mpr; intro n; rw [if_neg]; rintro ⟨-, h, -⟩; omega
  · obtain ⟨n, hn⟩ : ∃ n, ω (Fin.last (t + 1)) = n + 1 := ⟨ω (Fin.last (t + 1)) - 1, by omega⟩
    rw [tsum_eq_single n]
    · by_cases hc : ω 0 = 0 ∧ ∀ i : Fin (t + 2), i ≠ 0 → ω i ≠ 0
      · rw [if_pos hc, if_pos ⟨hc.1, hn, fun m hm _ => Nat.pos_of_ne_zero (hc.2 m hm)⟩]
      · rw [if_neg hc, if_neg]
        rintro ⟨h1, -, h3⟩
        apply hc
        refine ⟨h1, fun i hi => ?_⟩
        by_cases hil : i = Fin.last (t + 1)
        · rw [hil, hn]; omega
        · exact (h3 i hi hil).ne'
    · intro k hk; rw [if_neg]; rintro ⟨-, h2, -⟩; omega

lemma g77c_SAE_tsum (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    ∑' t, g71y_SAE P 0 t = 1 + ∑' k, ∏ i ∈ Finset.range (k + 1), g77c_RE P i := by
  rw [tsum_eq_zero_add' ENNReal.summable, g77c_SAE_zero]
  congr 1
  simp_rw [g77c_SAE_succ P]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  exact g77c_VE_prod P hP k

lemma g77c_summ_iff (f : ℕ → ℝ≥0∞) (hf : ∀ n, f n ≠ ⊤) :
    Summable (fun n => (f n).toReal) ↔ ∑' n, f n ≠ ⊤ := by
  constructor
  · intro h
    have e : ∑' n, f n = ENNReal.ofReal (∑' n, (f n).toReal) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => ENNReal.toReal_nonneg) h]
      exact tsum_congr fun n => (ENNReal.ofReal_toReal (hf n)).symm
    rw [e]; exact ENNReal.ofReal_ne_top
  · exact ENNReal.summable_toReal

lemma g77c_PR_iff (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    PositiveRecurrent P 0 ↔ Summable (fun k => ∏ i ∈ Finset.range (k + 1), R P (i + 1)) := by
  have hPR : PositiveRecurrent P 0 ↔ Summable (fun t => (g71y_SAE P 0 t).toReal) := by
    unfold PositiveRecurrent returnTailC
    simp_rw [g71y_SA_eq P hP.stochastic.1]
  rw [hPR, g77c_summ_iff _ (fun t => ne_top_of_le_ne_top ENNReal.one_ne_top (g77c_SAE_le P hP 0 t)),
    g77c_SAE_tsum P hP]
  have hpt : ∀ k, ∏ i ∈ Finset.range (k + 1), g77c_RE P i ≠ ⊤ :=
    fun k => ENNReal.prod_ne_top (fun i _ => g77c_RE_ne_top P hP i)
  have e : (fun k => ∏ i ∈ Finset.range (k + 1), R P (i + 1)) =
      fun k => (∏ i ∈ Finset.range (k + 1), g77c_RE P i).toReal := by
    funext k; rw [ENNReal.toReal_prod]; exact Finset.prod_congr rfl fun i _ => g77c_R_eq P hP i
  rw [e, g77c_summ_iff _ hpt, ENNReal.add_ne_top]
  simp

lemma g77c_G_chain (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    G P (m + 1) = 1 ↔ G P (m + 2) = 1 := by
  obtain ⟨-, e, -, -, -⟩ := g77c_rel P hP m
  have r3 := g77c_row3 P hP m
  have hd := hP.down_pos m
  have hu := hP.up_pos (m + 1)
  constructor
  · intro h; rw [h] at e
    have : P (m + 1) (m + 2) * (G P (m + 2) - 1) = 0 := by linear_combination -e - r3
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  · intro h; rw [h] at e
    have : P (m + 1) m * (G P (m + 1) - 1) = 0 := by linear_combination e + G P (m + 1) * r3
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith

lemma g77c_G_all (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    G P 1 = 1 ↔ ∀ m, G P (m + 1) = 1 := by
  refine ⟨fun h m => ?_, fun h => h 0⟩
  induction m with
  | zero => exact h
  | succ m ih => exact (g77c_G_chain P hP m).mp ih

lemma g77c_G_one_iff_R (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    G P (m + 1) = 1 ↔ R P (m + 1) = P m (m + 1) / P (m + 1) m := by
  obtain ⟨e, -⟩ := g77c_rel P hP m
  have hd := hP.down_pos m; have hu := hP.up_pos m
  rw [eq_div_iff hd.ne']
  constructor
  · intro h; rw [h] at e; linarith
  · intro h; rw [h] at e
    exact mul_left_cancel₀ hu.ne' (e.trans (mul_one _).symm)

lemma g77c_R_le (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    0 ≤ R P (m + 1) ∧ R P (m + 1) ≤ P m (m + 1) / P (m + 1) m := by
  obtain ⟨e, -, hg0, hg1, hr0⟩ := g77c_rel P hP m
  have hd := hP.down_pos m; have hu := hP.up_pos m
  refine ⟨hr0, ?_⟩
  rw [le_div_iff₀ hd]; nlinarith

lemma g77c_rec_R (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
    Recurrent P 0 ↔ ∀ n : ℕ, R P (n + 1) = P n (n + 1) / P (n + 1) n := by
  rw [g71y_rec_iff P hP, g77c_G_all P hP]
  exact forall_congr' fun m => g77c_G_one_iff_R P hP m

lemma g77c_PR_rec (P : ℕ → ℕ → ℝ) (h : PositiveRecurrent P 0) : Recurrent P 0 :=
  h.tendsto_atTop_zero

lemma g77c_stat_fin (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (π : ℕ → ℝ)
    (hst : ∀ y, HasSum (fun x => π x * P x y) (π y)) (y : ℕ) :
    π y = ∑ x ∈ Finset.range (y + 2), π x * P x y := by
  refine (hst y).unique (hasSum_sum_of_ne_finset_zero fun x hx => ?_)
  rw [Finset.mem_range, not_lt] at hx
  rw [hP.skipFree x y (Or.inr (by omega)), mul_zero]

lemma g77c_stat_db (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (π : ℕ → ℝ)
    (hst : ∀ y, HasSum (fun x => π x * P x y) (π y)) (n : ℕ) :
    π (n + 1) * P (n + 1) n = π n * P n (n + 1) := by
  induction n with
  | zero =>
    have h := g77c_stat_fin P hP π hst 0
    have r0 := g77c_row0 P hP
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
    show π 1 * P 1 0 = π 0 * P 0 1
    linear_combination -h - π 0 * r0
  | succ n ih =>
    have h := g77c_stat_fin P hP π hst (n + 1)
    have r3 := g77c_row3 P hP n
    rw [show n + 1 + 2 = n + 3 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_eq_zero (fun x hx => by
        rw [Finset.mem_range] at hx; rw [hP.skipFree x (n + 1) (Or.inl (by omega)), mul_zero]),
      zero_add] at h
    show π (n + 2) * P (n + 2) (n + 1) = π (n + 1) * P (n + 1) (n + 2)
    linear_combination -h + ih - π (n + 1) * r3

/-- detailed balance for all pairs from the nearest-neighbour version. -/
lemma g77c_db_all (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (v : ℕ → ℝ)
    (hv : ∀ n, v (n + 1) * P (n + 1) n = v n * P n (n + 1)) (x y : ℕ) :
    v x * P x y = v y * P y x := by
  rcases lt_trichotomy x y with h | h | h
  · by_cases hxy : y = x + 1
    · subst hxy; rw [hv x]
    · rw [hP.skipFree x y (Or.inl (by omega)), hP.skipFree y x (Or.inr (by omega))]; ring
  · subst h; rfl
  · by_cases hxy : x = y + 1
    · subst hxy; rw [hv y]
    · rw [hP.skipFree x y (Or.inr (by omega)), hP.skipFree y x (Or.inl (by omega))]; ring

lemma g77c_db_stat (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (v : ℕ → ℝ)
    (hv : ∀ n, v (n + 1) * P (n + 1) n = v n * P n (n + 1)) (y : ℕ) :
    HasSum (fun x => v x * P x y) (v y) := by
  have e : (fun x => v x * P x y) = fun x => v y * P y x :=
    funext fun x => g77c_db_all P hP v hv x y
  rw [e]
  simpa using (hP.stochastic.2 y).mul_left (v y)

lemma g77c_hom_GR {b₀ a₀ a₁ a₂ : ℝ} (h : IsHomParams b₀ a₀ a₁ a₂) (n : ℕ) (hn : 1 ≤ n) :
    G (homP b₀ a₀ a₁ a₂) n = min 1 (a₂ / a₀) ∧ R (homP b₀ a₀ a₁ a₂) n = min 1 (a₀ / a₂) := by
  obtain ⟨h1, h2⟩ := g71y_GR_at_one b₀ a₀ a₁ a₂ h n hn
  have eG : Gz (homP b₀ a₀ a₁ a₂) n 1 = ((G (homP b₀ a₀ a₁ a₂) n : ℝ) : ℂ) := by
    unfold Gz G; simp only [one_pow, one_mul]; rw [Complex.ofReal_tsum]
  have eR : Rz (homP b₀ a₀ a₁ a₂) n 1 = ((R (homP b₀ a₀ a₁ a₂) n : ℝ) : ℂ) := by
    unfold Rz R; simp only [one_pow, one_mul]; rw [Complex.ofReal_tsum]
  rw [eG] at h1; rw [eR] at h2
  exact ⟨Complex.ofReal_injective h1, Complex.ofReal_injective h2⟩

lemma g77c_hom_PR {b₀ a₀ a₁ a₂ : ℝ} (h : IsHomParams b₀ a₀ a₁ a₂) :
    PositiveRecurrent (homP b₀ a₀ a₁ a₂) 0 ↔ a₀ < a₂ := by
  have hP := g71y_hom_bd h
  have ha0 := h.a₀_pos; have ha2 := h.a₂_pos
  rw [g77c_PR_iff _ hP]
  have e : (fun k => ∏ i ∈ Finset.range (k + 1), R (homP b₀ a₀ a₁ a₂) (i + 1)) =
      fun k => (min 1 (a₀ / a₂)) ^ (k + 1) := by
    funext k
    rw [Finset.prod_congr rfl (fun i _ => (g77c_hom_GR h (i + 1) (by omega)).2),
      Finset.prod_const, Finset.card_range]
  rw [e, summable_nat_add_iff 1 (f := fun k => (min 1 (a₀ / a₂)) ^ k),
    summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_nonneg (le_min zero_le_one (by positivity)), min_lt_iff, div_lt_one ha2]
  simp

lemma g77c_step_eq (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (x : ℕ) :
    ∀ t y, stepPow P t x y = (g71y_PS P x t y (fun _ => True)).toReal := by
  classical
  have h0 := hP.stochastic.1
  intro t
  induction t with
  | zero =>
    intro y
    rw [g71y_PS_zero]
    simp only [stepPow]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg (Ne.symm hxy), if_neg hxy]; simp
  | succ t ih =>
    intro y
    simp only [stepPow]
    rw [g71y_PS_snoc P h0, ENNReal.tsum_toReal_eq]
    · refine tsum_congr fun z => ?_
      rw [ih z, if_pos (Or.inr trivial), ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 _ _)]
    · intro z
      refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
      split_ifs
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _)
      · exact ENNReal.zero_ne_top

lemma g77c_step_mass (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (x : ℕ) :
    ∀ t, ∑' y, g71y_PS P x t y (fun _ => True) = 1 := by
  classical
  have h0 := hP.stochastic.1
  intro t
  induction t with
  | zero =>
    simp_rw [g71y_PS_zero]
    rw [tsum_eq_single x (fun b hb => by rw [if_neg (Ne.symm hb)])]; simp
  | succ t ih =>
    simp_rw [g71y_PS_snoc P h0 x t, if_pos (Or.inr trivial)]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, g71y_rowsum P hP, mul_one]
    exact ih

lemma g77c_rev (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (v : ℕ → ℝ)
    (hv : ∀ x z, v x * P x z = v z * P z x) (hv0 : ∀ x, 0 ≤ v x) :
    ∀ t x y, ENNReal.ofReal (v x) * g71y_PS P x t y (fun _ => True) =
      ENNReal.ofReal (v y) * g71y_PS P y t x (fun _ => True) := by
  classical
  have h0 := hP.stochastic.1
  intro t
  induction t with
  | zero =>
    intro x y
    rw [g71y_PS_zero, g71y_PS_zero]
    by_cases hxy : x = y
    · subst hxy; rfl
    · rw [if_neg hxy, if_neg (Ne.symm hxy)]; simp
  | succ t ih =>
    intro x y
    rw [g71y_PS_cons P h0 x t, g71y_PS_snoc P h0 y t]
    simp only [if_pos (Or.inr trivial)]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun z => ?_
    calc ENNReal.ofReal (v x) * (ENNReal.ofReal (P x z) * g71y_PS P z t y (fun _ => True))
        = ENNReal.ofReal (v x * P x z) * g71y_PS P z t y (fun _ => True) := by
          rw [ENNReal.ofReal_mul (hv0 x)]; ring
      _ = ENNReal.ofReal (v z * P z x) * g71y_PS P z t y (fun _ => True) := by rw [hv x z]
      _ = ENNReal.ofReal (P z x) * (ENNReal.ofReal (v z) * g71y_PS P z t y (fun _ => True)) := by
          rw [ENNReal.ofReal_mul (hv0 z)]; ring
      _ = ENNReal.ofReal (P z x) * (ENNReal.ofReal (v y) * g71y_PS P y t z (fun _ => True)) := by
          rw [ih z y]
      _ = _ := by ring

lemma g77c_limit (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P)
    (π : ℕ → ℝ)
    (hπ : ∀ n : ℕ, Filter.Tendsto (fun k : ℕ => stepPow P k 0 n) Filter.atTop (nhds (π n))) :
    (∀ n : ℕ, π (n + 1) = π n * R P (n + 1)) ∧
    (PositiveRecurrent P 0 ↔
      Summable (fun k : ℕ => ∏ i ∈ Finset.range (k + 1), R P (i + 1))) ∧
    (PositiveRecurrent P 0 →
      π 0 = (1 + ∑' k : ℕ, ∏ i ∈ Finset.range (k + 1), R P (i + 1))⁻¹) := by
  classical
  have h0 := hP.stochastic.1
  have hstep := g77c_step_eq P hP 0
  have hsp0 : ∀ t y, 0 ≤ stepPow P t 0 y := fun t y => by rw [hstep]; exact ENNReal.toReal_nonneg
  have hsp1 : ∀ t y, stepPow P t 0 y ≤ 1 := fun t y => by
    rw [hstep]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using g71y_PS_le P hP _ _ _ _)
  have part1 : ∀ n : ℕ, π (n + 1) = π n * R P (n + 1) := by
    intro n
    set ρ : ℕ → ℝ := fun j => r P (n + 1) (j + 1) with hρ
    have hρe : ∀ j, ρ j = (g71y_PS P n (j + 1) (n + 1) (fun s => n < s)).toReal := by
      intro j; simp only [hρ, r]; rw [Nat.add_sub_cancel]; exact g71y_taboo_eq P h0 _ _ _ _
    have hρ0 : ∀ j, 0 ≤ ρ j := fun j => by rw [hρe]; exact ENNReal.toReal_nonneg
    have hρs : Summable ρ := by
      have := ENNReal.summable_toReal (g77c_RE_ne_top P hP n)
      convert this using 1; funext j; exact hρe j
    have hR : R P (n + 1) = ∑' j, ρ j := rfl
    set f : ℕ → ℕ → ℝ := fun L j => if j ≤ L then stepPow P (L - j) 0 n * ρ j else 0 with hf
    have hfs : ∀ L, ∑' j, f L j = stepPow P (L + 1) 0 (n + 1) := by
      intro L
      rw [tsum_eq_sum (s := Finset.range (L + 1)) (fun j hj => by
        simp only [hf]; rw [if_neg (by simpa using hj)])]
      have e1 : ∀ L', g71y_PS P 0 (L' + 1) (n + 1) (fun _ => True) =
          ∑ s ∈ Finset.range (L' + 1), g71y_PS P 0 s n (fun _ => True) *
            g71y_PS P n (L' + 1 - s) (n + 1) (fun s => n < s) :=
        fun L' => g77c_lastexit P hP _ n 0 (fun _ _ => trivial) (by omega) L' (n + 1) le_rfl
      rw [hstep, e1, ENNReal.toReal_sum (fun s _ => ENNReal.mul_ne_top
        (ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _))
        (ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _)))]
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      simp only [hf]
      rw [if_pos (by omega), ENNReal.toReal_mul, hstep, hρe]
      congr 3 <;> first | omega | rfl
    have hlim : Filter.Tendsto (fun L => ∑' j, f L j) Filter.atTop (nhds (∑' j, π n * ρ j)) := by
      refine tendsto_tsum_of_dominated_convergence hρs (fun j => ?_) ?_
      · have : Filter.Tendsto (fun L => stepPow P (L - j) 0 n * ρ j) Filter.atTop
            (nhds (π n * ρ j)) :=
          ((hπ n).comp (Filter.tendsto_sub_atTop_nat j)).mul_const _
        refine this.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop j] with L hL
        simp only [hf, if_pos hL]
      · refine Filter.Eventually.of_forall fun L j => ?_
        simp only [hf]
        split_ifs
        · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hsp0 _ _) (hρ0 j))]
          exact mul_le_of_le_one_left (hρ0 j) (hsp1 _ _)
        · simp [hρ0 j]
    simp_rw [hfs] at hlim
    have h2 := (hπ (n + 1)).comp (Filter.tendsto_add_atTop_nat 1)
    rw [tsum_mul_left] at hlim
    exact tendsto_nhds_unique h2 hlim
  refine ⟨part1, g77c_PR_iff P hP, fun hPR => ?_⟩
  have hrec := (g77c_rec_R P hP).mp (g77c_PR_rec P hPR)
  have hs := (g77c_PR_iff P hP).mp hPR
  set w : ℕ → ℝ := fun n => ∏ i ∈ Finset.range n, R P (i + 1) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => Finset.prod_nonneg fun i _ => (g77c_R_le P hP i).1
  have hws : Summable w := (summable_nat_add_iff 1).mp hs
  set S := ∑' k, ∏ i ∈ Finset.range (k + 1), R P (i + 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => Finset.prod_nonneg fun i _ => (g77c_R_le P hP i).1
  have hwsum : ∑' n, w n = 1 + S := by rw [hws.tsum_eq_zero_add]; simp [hw, hS]
  have hwdb : ∀ n, w (n + 1) * P (n + 1) n = w n * P n (n + 1) := by
    intro n
    show (∏ i ∈ Finset.range (n + 1), R P (i + 1)) * P (n + 1) n =
      (∏ i ∈ Finset.range n, R P (i + 1)) * P n (n + 1)
    rw [Finset.prod_range_succ, mul_assoc, hrec n, div_mul_cancel₀ _ (hP.down_pos n).ne']
  have hbd : ∀ t n, stepPow P t 0 n ≤ w n := by
    intro t n
    have := g77c_rev P hP w (g77c_db_all P hP w hwdb) hw0 t 0 n
    have hw00 : w 0 = 1 := by simp [hw]
    rw [hw00, ENNReal.ofReal_one, one_mul] at this
    rw [hstep, this]
    refine ENNReal.toReal_le_of_le_ofReal (hw0 n) ?_
    calc ENNReal.ofReal (w n) * g71y_PS P n t 0 (fun _ => True) ≤ ENNReal.ofReal (w n) * 1 := by
          gcongr; exact g71y_PS_le P hP _ _ _ _
      _ = ENNReal.ofReal (w n) := mul_one _
  have hmass : ∀ t, ∑' n, stepPow P t 0 n = 1 := by
    intro t
    simp_rw [hstep]
    rw [← ENNReal.tsum_toReal_eq (fun y => ne_top_of_le_ne_top ENNReal.one_ne_top
      (g71y_PS_le P hP _ _ _ _)), g77c_step_mass P hP 0 t, ENNReal.toReal_one]
  have hlim : Filter.Tendsto (fun t => ∑' n, stepPow P t 0 n) Filter.atTop (nhds (∑' n, π n)) := by
    refine tendsto_tsum_of_dominated_convergence hws hπ ?_
    refine Filter.Eventually.of_forall fun t n => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hsp0 _ _)]
    exact hbd t n
  simp_rw [hmass] at hlim
  have hsum1 : ∑' n, π n = 1 := (tendsto_nhds_unique hlim tendsto_const_nhds)
  have hform : ∀ n, π n = π 0 * w n := by
    intro n
    induction n with
    | zero => simp [hw]
    | succ n ih =>
      rw [part1 n, ih]
      show π 0 * (∏ i ∈ Finset.range n, R P (i + 1)) * R P (n + 1) =
        π 0 * ∏ i ∈ Finset.range (n + 1), R P (i + 1)
      rw [Finset.prod_range_succ, mul_assoc]
  have h3 : π 0 * (1 + S) = 1 := by
    rw [← hwsum, ← tsum_mul_left, ← hsum1]
    exact tsum_congr fun n => (hform n).symm
  exact eq_inv_of_mul_eq_one_left h3

theorem solution (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂)
    (hap : AperiodicC (homP b₀ a₀ a₁ a₂)) (π : ℕ → ℝ)
    (hπ : ∀ n : ℕ, Filter.Tendsto (fun k : ℕ => stepPow (homP b₀ a₀ a₁ a₂) k 0 n)
      Filter.atTop (nhds (π n))) :
    (∀ n : ℕ, R (homP b₀ a₀ a₁ a₂) (n + 1) = R (homP b₀ a₀ a₁ a₂) 1) ∧
    (∀ n : ℕ, π (n + 1) = π n * R (homP b₀ a₀ a₁ a₂) 1) ∧
    (PositiveRecurrent (homP b₀ a₀ a₁ a₂) 0 →
      R (homP b₀ a₀ a₁ a₂) 1 = a₀ / a₂ ∧
      ∀ n : ℕ, π n = (1 - R (homP b₀ a₀ a₁ a₂) 1) * R (homP b₀ a₀ a₁ a₂) 1 ^ n) := by
  have hP := g71y_hom_bd h
  have ha0 := h.a₀_pos; have ha2 := h.a₂_pos
  obtain ⟨p1, -, p3⟩ := g77c_limit _ hP π hπ
  have hRn : ∀ n, R (homP b₀ a₀ a₁ a₂) (n + 1) = R (homP b₀ a₀ a₁ a₂) 1 := fun n => by
    rw [(g77c_hom_GR h (n + 1) (by omega)).2, (g77c_hom_GR h 1 le_rfl).2]
  have hstep : ∀ n, π (n + 1) = π n * R (homP b₀ a₀ a₁ a₂) 1 := fun n => by rw [p1 n, hRn n]
  refine ⟨hRn, hstep, fun hPR => ?_⟩
  have hlt := (g77c_hom_PR h).mp hPR
  have hR1 : R (homP b₀ a₀ a₁ a₂) 1 = a₀ / a₂ := by
    rw [(g77c_hom_GR h 1 le_rfl).2, min_eq_right ((div_le_one ha2).mpr hlt.le)]
  refine ⟨hR1, ?_⟩
  set ρ := R (homP b₀ a₀ a₁ a₂) 1 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hR1]; positivity
  have hρ1 : ρ < 1 := by rw [hR1]; exact (div_lt_one ha2).mpr hlt
  have hpow : ∀ n, π n = π 0 * ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hstep n, ih, pow_succ, mul_assoc]
  have h0 := p3 hPR
  have e : (fun k => ∏ i ∈ Finset.range (k + 1), R (homP b₀ a₀ a₁ a₂) (i + 1)) =
      fun k => ρ ^ (k + 1) := by
    funext k
    rw [Finset.prod_congr rfl (fun i _ => hRn i), Finset.prod_const, Finset.card_range]
  rw [e] at h0
  have hs : ∑' k, ρ ^ (k + 1) = ρ * (1 - ρ)⁻¹ := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1, mul_comm]
  rw [hs] at h0
  have hne : (1 - ρ) ≠ 0 := by linarith
  have h1 : 1 + ρ * (1 - ρ)⁻¹ = (1 - ρ)⁻¹ := by field_simp; ring
  rw [h1, inv_inv] at h0
  intro n
  rw [hpow n, h0]
