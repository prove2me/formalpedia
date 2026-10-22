-- Prove2me | solution 1 for MatrixAnalytic.BirthDeath.gf_relations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:09:00.138094+00:00
-- url     : https://prove2.me/submissions/f3d3699f-f706-4701-9b4f-67a4d93611dd

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

lemma g71y_rowsum (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (y : ℕ) :
    ∑' x, ENNReal.ofReal (P y x) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => hP.stochastic.1 y x)
    (hP.stochastic.2 y).summable, (hP.stochastic.2 y).tsum_eq, ENNReal.ofReal_one]


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

noncomputable def g71y_gf (c : ℕ → ℝ≥0∞) (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ (k + 1) * (((c (k + 1)).toReal : ℝ) : ℂ)

lemma g71y_toReal_le (a : ℝ≥0∞) (h : a ≤ 1) : a.toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

lemma g71y_gf_norm (c : ℕ → ℝ≥0∞) (hc : ∀ k, c k ≤ 1) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => ‖z ^ (k + 1) * (((c (k + 1)).toReal : ℝ) : ℂ)‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, pow_succ', mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (by positivity)
    (g71y_toReal_le _ (hc _))) (norm_nonneg _)

lemma g71y_gf_shift (c : ℕ → ℝ≥0∞) (hc : ∀ k, c k ≤ 1) (z : ℂ) (hz : ‖z‖ < 1) :
    g71y_gf c z = z * (((c 1).toReal : ℝ) : ℂ) +
      ∑' k : ℕ, z ^ (k + 1 + 1) * (((c (k + 1 + 1)).toReal : ℝ) : ℂ) := by
  unfold g71y_gf
  rw [(g71y_gf_norm c hc z hz).of_norm.tsum_eq_zero_add]
  simp

lemma g71y_gf_mul (a b : ℕ → ℝ≥0∞) (ha : ∀ k, a k ≤ 1) (hb : ∀ k, b k ≤ 1) (z : ℂ) (hz : ‖z‖ < 1) :
    g71y_gf a z * g71y_gf b z = ∑' k : ℕ, z ^ (k + 1 + 1) *
      ∑ s ∈ Finset.range (k + 1), ((((a (s + 1)).toReal : ℝ) : ℂ) * (((b (k - s + 1)).toReal : ℝ) : ℂ)) := by
  unfold g71y_gf
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (g71y_gf_norm a ha z hz)
    (g71y_gf_norm b hb z hz)]
  refine tsum_congr fun k => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => z ^ (i + 1) * (((a (i + 1)).toReal : ℝ) : ℂ) * (z ^ (j + 1) * (((b (j + 1)).toReal : ℝ) : ℂ))) k,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [show k + 1 + 1 = (s + 1) + (k - s + 1) by omega, pow_add]
  ring

lemma g71y_toReal_sum_mul (s : Finset ℕ) (f g : ℕ → ℝ≥0∞) (hf : ∀ k, f k ≤ 1) (hg : ∀ k, g k ≤ 1) :
    ((∑ i ∈ s, f i * g i).toReal : ℂ) = ∑ i ∈ s, ((f i).toReal : ℂ) * ((g i).toReal : ℂ) := by
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hf i))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hg i)))]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_mul]; push_cast; rfl

theorem solution (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : ‖z‖ < 1) :
    Uz P n z = z * P n n + z * P n (n + 1) * Gz P (n + 1) z ∧
    Uz P n z = z * P n n + Rz P (n + 1) z * z * P (n + 1) n ∧
    Uz P n z ≠ 1 ∧
    Gz P n z = (1 - Uz P n z)⁻¹ * z * P n (n - 1) ∧
    Rz P n z = z * P (n - 1) n * (1 - Uz P n z)⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 := hP.stochastic.1
  simp only [Nat.add_sub_cancel]
  have hle := g71y_PS_le P hP
  have hG : Gz P (m + 1) z = g71y_gf (fun k => g71y_PS P (m + 1) k m (fun s => m < s)) z := by
    unfold Gz g g71y_gf; simp only [Nat.add_sub_cancel]
    refine tsum_congr fun k => ?_; rw [g71y_taboo_eq P h0]
  have hG1 : Gz P (m + 1 + 1) z =
      g71y_gf (fun k => g71y_PS P (m + 1 + 1) k (m + 1) (fun s => m + 1 < s)) z := by
    unfold Gz g g71y_gf; simp only [Nat.add_sub_cancel]
    refine tsum_congr fun k => ?_; rw [g71y_taboo_eq P h0]
  have hU : Uz P (m + 1) z = g71y_gf (fun k => g71y_PS P (m + 1) k (m + 1) (fun s => m + 1 < s)) z := by
    unfold Uz u g71y_gf
    refine tsum_congr fun k => ?_; rw [g71y_taboo_eq P h0]
  have hR : Rz P (m + 1) z = g71y_gf (fun k => g71y_PS P m k (m + 1) (fun s => m < s)) z := by
    unfold Rz r g71y_gf; simp only [Nat.add_sub_cancel]
    refine tsum_congr fun k => ?_; rw [g71y_taboo_eq P h0]
  have hR1 : Rz P (m + 1 + 1) z =
      g71y_gf (fun k => g71y_PS P (m + 1) k (m + 1 + 1) (fun s => m + 1 < s)) z := by
    unfold Rz r g71y_gf; simp only [Nat.add_sub_cancel]
    refine tsum_congr fun k => ?_; rw [g71y_taboo_eq P h0]
  -- identity 1
  have e1 : Uz P (m + 1) z = z * P (m + 1) (m + 1) + z * P (m + 1) (m + 1 + 1) * Gz P (m + 1 + 1) z := by
    rw [hU, hG1, g71y_gf_shift _ (fun k => hle _ _ _ _) z hz, g71y_PS_one P h0,
      ENNReal.toReal_ofReal (h0 _ _)]
    congr 1
    unfold g71y_gf
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [g71y_id1 P hP (m + 1) k, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 _ _)]
    push_cast; ring
  have e2 : Uz P (m + 1) z = z * P (m + 1) (m + 1) + Rz P (m + 1 + 1) z * z * P (m + 1 + 1) (m + 1) := by
    rw [hU, hR1, g71y_gf_shift _ (fun k => hle _ _ _ _) z hz, g71y_PS_one P h0,
      ENNReal.toReal_ofReal (h0 _ _)]
    congr 1
    unfold g71y_gf
    rw [← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    rw [g71y_id2 P hP (m + 1) k, ENNReal.toReal_mul, ENNReal.toReal_ofReal (h0 _ _)]
    push_cast; ring
  have e4 : Gz P (m + 1) z = z * P (m + 1) m + Uz P (m + 1) z * Gz P (m + 1) z := by
    rw [hU, hG, g71y_gf_mul _ _ (fun k => hle _ _ _ _) (fun k => hle _ _ _ _) z hz,
      g71y_gf_shift _ (fun k => hle _ _ _ _) z hz, g71y_PS_one P h0, ENNReal.toReal_ofReal (h0 _ _)]
    congr 1
    refine tsum_congr fun k => ?_
    rw [g71y_conv4 P hP m (k + 1) (m + 1) le_rfl, if_neg (by omega), zero_add,
      g71y_toReal_sum_mul _ _ _ (fun _ => hle _ _ _ _) (fun _ => hle _ _ _ _)]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show k + 1 - s = k - s + 1 by omega]
  have e5 : Rz P (m + 1) z = z * P m (m + 1) + Uz P (m + 1) z * Rz P (m + 1) z := by
    rw [hU, hR, g71y_gf_mul _ _ (fun k => hle _ _ _ _) (fun k => hle _ _ _ _) z hz,
      g71y_gf_shift _ (fun k => hle _ _ _ _) z hz, g71y_PS_one P h0, ENNReal.toReal_ofReal (h0 _ _)]
    congr 1
    refine tsum_congr fun k => ?_
    rw [g71y_conv5 P hP m (k + 1) (m + 1) le_rfl, if_neg (by omega), zero_add,
      g71y_toReal_sum_mul _ _ _ (fun _ => hle _ _ _ _) (fun _ => hle _ _ _ _)]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : s ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    rw [show k + 1 - s = k - s + 1 by omega, mul_comm]
  have hpos : (P (m + 1) m : ℂ) ≠ 0 := by
    exact_mod_cast (hP.down_pos m).ne'
  have hUne : Uz P (m + 1) z ≠ 1 := by
    intro h1
    rw [h1, one_mul] at e4
    have hz0 : z * P (m + 1) m = 0 := by linear_combination -e4
    have hz0' : z = 0 := (mul_eq_zero.mp hz0).resolve_right hpos
    rw [hU, hz0'] at h1
    unfold g71y_gf at h1
    simp at h1
  have h1u : 1 - Uz P (m + 1) z ≠ 0 := sub_ne_zero.mpr (Ne.symm hUne)
  refine ⟨e1, e2, hUne, ?_, ?_⟩
  · rw [eq_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀ h1u]
    linear_combination -e4
  · rw [eq_mul_inv_iff_mul_eq₀ h1u]
    linear_combination e5
