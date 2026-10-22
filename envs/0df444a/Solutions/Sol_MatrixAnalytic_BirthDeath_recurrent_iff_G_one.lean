-- Prove2me | solution 1 for MatrixAnalytic.BirthDeath.recurrent_iff_G_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:47:52.088782+00:00
-- url     : https://prove2.me/submissions/a11e0a05-f0a0-4d6c-bfa6-cae901fea11a

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

theorem solution (P : ℕ → ℕ → ℝ) (hP : IsBirthDeath P) :
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
