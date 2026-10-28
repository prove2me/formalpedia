-- Prove2me | solution 2 for MatrixAnalytic.BirthDeath.homogeneous_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:51.679669+00:00
-- url     : https://prove2.me/submissions/690f1175-155a-4ac3-8cf4-50dd34900c0b

import Mathlib
import Definitions.Def_MatrixAnalytic_BirthDeath_Chain
import Definitions.Def_MatrixAnalytic_BirthDeath_Model
import Definitions.Def_MatrixAnalytic_BirthDeath_Passage
import Theorems.Thm_MatrixAnalytic_BirthDeath_G_R_at_one

-- carved verbatim out of submission 6e37eeca-82ea-453b-b796-566525e4ff4e, lines 1303-1334

section
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

end

section
open MatrixAnalytic.BirthDeath
open scoped ENNReal
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

end

section
open MatrixAnalytic.BirthDeath
open scoped ENNReal

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

lemma g77c_R_eq (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (m : ℕ) :
    R P (m + 1) = (g77c_RE P m).toReal := by
  unfold R r g77c_RE
  rw [ENNReal.tsum_toReal_eq (fun k => ne_top_of_le_ne_top ENNReal.one_ne_top (g71y_PS_le P hP _ _ _ _))]
  refine tsum_congr fun k => ?_
  simp only [Nat.add_sub_cancel]
  exact g71y_taboo_eq P hP.stochastic.1 _ _ _ _

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

lemma g77c_hom_GR {b₀ a₀ a₁ a₂ : ℝ} (h : IsHomParams b₀ a₀ a₁ a₂) (n : ℕ) (hn : 1 ≤ n) :
    G (homP b₀ a₀ a₁ a₂) n = min 1 (a₂ / a₀) ∧ R (homP b₀ a₀ a₁ a₂) n = min 1 (a₀ / a₂) := by
  obtain ⟨h1, h2⟩ := MatrixAnalytic.BirthDeath.G_R_at_one b₀ a₀ a₁ a₂ h n hn
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

theorem solution (b₀ a₀ a₁ a₂ : ℝ) (h : IsHomParams b₀ a₀ a₁ a₂) :
    (Recurrent (homP b₀ a₀ a₁ a₂) 0 ↔ a₀ ≤ a₂) ∧
    (PositiveRecurrent (homP b₀ a₀ a₁ a₂) 0 ↔ a₀ < a₂) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 ≤ G (homP b₀ a₀ a₁ a₂) n ∧
      G (homP b₀ a₀ a₁ a₂) n =
        a₂ + a₁ * G (homP b₀ a₀ a₁ a₂) n + a₀ * G (homP b₀ a₀ a₁ a₂) n ^ 2 ∧
      ∀ x : ℝ, 0 ≤ x → x = a₂ + a₁ * x + a₀ * x ^ 2 → G (homP b₀ a₀ a₁ a₂) n ≤ x := by
  have hP := g71y_hom_bd h
  have ha0 := h.a₀_pos; have ha1 := h.a₁_nonneg; have ha2 := h.a₂_pos; have hrs := h.row_sum
  refine ⟨?_, g77c_hom_PR h, fun n hn => ?_⟩
  · rw [g71y_rec_iff _ hP, (g77c_hom_GR h 1 le_rfl).1, min_eq_left_iff, one_le_div ha0]
  · rw [(g77c_hom_GR h n hn).1]
    have key : ∀ x : ℝ, x = a₂ + a₁ * x + a₀ * x ^ 2 → (x - 1) * (a₀ * x - a₂) = 0 := by
      intro x hx; linear_combination -hx - x * hrs
    rcases le_or_gt a₀ a₂ with hle | hlt
    · rw [min_eq_left ((one_le_div ha0).mpr hle)]
      refine ⟨zero_le_one, by linear_combination -hrs, fun x hx0 hx => ?_⟩
      rcases mul_eq_zero.mp (key x hx) with h1 | h1
      · linarith
      · have : x = a₂ / a₀ := by field_simp; linarith
        rw [this]; exact (one_le_div ha0).mpr hle
    · have hlt' : a₂ / a₀ < 1 := (div_lt_one ha0).mpr hlt
      rw [min_eq_right hlt'.le]
      set γ := a₂ / a₀ with hγ
      have hg : a₀ * γ = a₂ := by rw [hγ]; field_simp
      refine ⟨by positivity, by linear_combination (1 - γ) * hg - γ * hrs, fun x hx0 hx => ?_⟩
      rcases mul_eq_zero.mp (key x hx) with h1 | h1
      · linarith
      · have : x = γ := by rw [hγ]; field_simp; linarith
        rw [this]

end
