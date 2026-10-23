-- Prove2me | solution 1 for MNLBandit.LowerBound.lemma_E_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:07:49.635532+00:00
-- url     : https://prove2.me/submissions/13313bd7-c198-4098-bc3e-4e169b0208f7

import Mathlib
import Definitions.Def_MNLBandit_LowerBound_BernoulliMAB



namespace MNLBandit.LowerBound

open Finset

lemma g57_prefixOf_snoc_castSucc {α : Type*} {s : ℕ} (h : Fin s → α) (x : α) (i : Fin s) :
    prefixOf (Fin.snoc h x : Fin (s+1) → α) (Fin.castSucc i) = prefixOf h i := by
  funext u
  simp only [prefixOf]
  have : (Fin.castLE (Fin.castSucc i).isLt.le u : Fin (s+1)) =
      Fin.castSucc (Fin.castLE i.isLt.le u) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma g57_prefixOf_snoc_last {α : Type*} {s : ℕ} (h : Fin s → α) (x : α) :
    prefixOf (Fin.snoc h x : Fin (s+1) → α) (Fin.last s) = h := by
  funext u
  simp only [prefixOf]
  have : (Fin.castLE (Fin.last s).isLt.le u : Fin (s+1)) = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma g57_mabLaw_snoc {N : ℕ} (A : MABAlg N) (μ : Fin N → ℝ) (s : ℕ)
    (h : Fin s → Fin N × Bool) (x : Fin N × Bool) :
    mabLaw A μ (s+1) (Fin.snoc h x) = mabLaw A μ s h * (A s h x.1 * bern (μ x.1) x.2) := by
  unfold mabLaw
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [g57_prefixOf_snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [g57_prefixOf_snoc_last, Fin.snoc_last]
    rfl

lemma g57_sum_snoc {X : Type*} [Fintype X] (s : ℕ) (F : (Fin (s+1) → X) → ℝ) :
    ∑ h, F h = ∑ h : Fin s → X, ∑ x, F (Fin.snoc h x) := by
  rw [← (Fin.snocEquiv (fun _ => X)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma g57_bern_sum (p : ℝ) : ∑ b : Bool, bern p b = 1 := by simp [bern]

lemma g57_step_sum {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ) (s : ℕ)
    (h : Fin s → Fin N × Bool) : ∑ x : Fin N × Bool, A s h x.1 * bern (μ x.1) x.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, g57_bern_sum, mul_one]
  exact (hA s h).2

lemma g57_M2 {N : ℕ} (A : MABAlg N) (μ : Fin N → ℝ) (s : ℕ)
    (G : (Fin s → Fin N × Bool) → Fin N × Bool → ℝ) :
    ∑ h : Fin (s+1) → Fin N × Bool, mabLaw A μ (s+1) h * G (Fin.init h) (h (Fin.last s)) =
    ∑ h : Fin s → Fin N × Bool, mabLaw A μ s h *
      ∑ x, A s h x.1 * bern (μ x.1) x.2 * G h x := by
  rw [g57_sum_snoc]
  apply sum_congr rfl
  intro h _
  rw [mul_sum]
  apply sum_congr rfl
  intro x _
  rw [g57_mabLaw_snoc, Fin.init_snoc, Fin.snoc_last]
  ring

lemma g57_M1 {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ) (s : ℕ)
    (F : (Fin s → Fin N × Bool) → ℝ) :
    ∑ h : Fin (s+1) → Fin N × Bool, mabLaw A μ (s+1) h * F (Fin.init h) =
    ∑ h : Fin s → Fin N × Bool, mabLaw A μ s h * F h := by
  have := g57_M2 A μ s (fun h _ => F h)
  try simp only at this
  rw [this]
  apply sum_congr rfl
  intro h _
  rw [← sum_mul, g57_step_sum A hA, one_mul]

lemma g57_law_sum {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ) :
    ∀ s, ∑ h : Fin s → Fin N × Bool, mabLaw A μ s h = 1
  | 0 => by simp [mabLaw]
  | s+1 => by
    have := g57_M1 A hA μ s (fun _ => 1)
    simp only [mul_one] at this
    rw [this, g57_law_sum A hA μ s]

lemma g57_M3 {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ) (t : ℕ)
    (F : (Fin t → Fin N × Bool) → ℝ) : ∀ s (hts : t ≤ s),
    ∑ h : Fin s → Fin N × Bool, mabLaw A μ s h * F (fun u => h (Fin.castLE hts u)) =
    ∑ h : Fin t → Fin N × Bool, mabLaw A μ t h * F h := by
  intro s
  induction s with
  | zero =>
    intro hts
    obtain rfl : t = 0 := by omega
    apply sum_congr rfl
    intro h _
    congr 2
  | succ s ih =>
    intro hts
    rcases Nat.lt_or_ge s t with hlt | hle
    · obtain rfl : t = s + 1 := by omega
      apply sum_congr rfl
      intro h _
      congr 2
    · have := g57_M1 A hA μ s (fun g => F (fun u => g (Fin.castLE hle u)))
      try simp only at this
      rw [← ih hle, ← this]
      apply sum_congr rfl
      intro h _
      congr 2

lemma g57_marg {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ) (T : ℕ) (t : Fin T)
    (φ : Fin N × Bool → ℝ) :
    ∑ h : Fin T → Fin N × Bool, mabLaw A μ T h * φ (h t) =
    ∑ h : Fin t → Fin N × Bool, mabLaw A μ t h *
      ∑ x, A t h x.1 * bern (μ x.1) x.2 * φ x := by
  have h1 := g57_M3 A hA μ (t+1) (fun g => φ (g (Fin.last t))) T t.isLt
  have h2 := g57_M2 A μ t (fun _ x => φ x)
  try simp only at h1 h2
  rw [← h2, ← h1]
  apply sum_congr rfl
  intro h _
  congr 3

lemma g57_bern_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) (b : Bool) : 0 < bern p b := by
  cases b <;> simp [bern] <;> linarith

lemma g57_tv {ι : Type*} [Fintype ι] (p R f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hR : ∀ i, 0 < R i)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hp1 : ∑ i, p i = 1)
    (hpR : ∑ i, p i * R i = 1) :
    (∑ i, p i * R i * f i - ∑ i, p i * f i) ^ 2 ≤ ∑ i, p i * (-Real.log (R i)) := by
  have e : ∀ i, (√(p i) * (√(R i) - 1)) * (√(p i) * (√(R i) + 1) * (f i - 1/2)) =
      (p i * R i * f i - p i * f i) - 1/2 * (p i * R i - p i) := by
    intro i
    have h1 := Real.mul_self_sqrt (hp i)
    have h2 := Real.mul_self_sqrt (hR i).le
    linear_combination (√(R i) * √(R i) - 1) * (f i - 1/2) * h1 + p i * (f i - 1/2) * h2
  have key : ∑ i, p i * R i * f i - ∑ i, p i * f i =
      ∑ i, (√(p i) * (√(R i) - 1)) * (√(p i) * (√(R i) + 1) * (f i - 1/2)) := by
    simp_rw [e]
    rw [sum_sub_distrib, ← mul_sum, sum_sub_distrib, sum_sub_distrib, hp1, hpR]
    ring
  have hb : ∑ i, (√(p i) * (√(R i) + 1) * (f i - 1/2)) ^ 2 ≤ 1 := by
    have : ∀ i, (√(p i) * (√(R i) + 1) * (f i - 1/2)) ^ 2 ≤ (p i * R i + p i) / 2 := by
      intro i
      rw [mul_pow, mul_pow, Real.sq_sqrt (hp i)]
      have hA : (√(R i) + 1) ^ 2 ≤ 2 * (R i + 1) := by
        nlinarith [sq_nonneg (√(R i) - 1), Real.sq_sqrt (hR i).le]
      have hB : (f i - 1/2) ^ 2 ≤ 1/4 := by nlinarith [hf0 i, hf1 i]
      calc p i * (√(R i) + 1) ^ 2 * (f i - 1/2) ^ 2
          = p i * ((√(R i) + 1) ^ 2 * (f i - 1/2) ^ 2) := by ring
        _ ≤ p i * (2 * (R i + 1) * (1/4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hA hB (sq_nonneg _) (by linarith [hR i])) (hp i)
        _ = (p i * R i + p i) / 2 := by ring
    calc _ ≤ ∑ i, (p i * R i + p i) / 2 := sum_le_sum fun i _ => this i
      _ = 1 := by rw [← sum_div, sum_add_distrib, hp1, hpR]; norm_num
  have ha : ∑ i, (√(p i) * (√(R i) - 1)) ^ 2 ≤ ∑ i, p i * (-Real.log (R i)) := by
    have e2 : ∀ i, (√(p i) * (√(R i) - 1)) ^ 2 = p i * (2 - 2 * √(R i)) + (p i * R i - p i) := by
      intro i
      rw [mul_pow, Real.sq_sqrt (hp i)]
      have h2 := Real.sq_sqrt (hR i).le
      linear_combination p i * h2
    simp_rw [e2]
    rw [sum_add_distrib, sum_sub_distrib, hp1, hpR, sub_self, add_zero]
    apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hp i)
    have hs : 0 < √(R i) := Real.sqrt_pos.mpr (hR i)
    have := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt (hR i).le] at this
    linarith
  rw [key]
  calc _ ≤ (∑ i, (√(p i) * (√(R i) - 1)) ^ 2) * ∑ i, (√(p i) * (√(R i) + 1) * (f i - 1/2)) ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, (√(p i) * (√(R i) - 1)) ^ 2) * 1 := by
        gcongr
    _ ≤ _ := by rw [mul_one]; exact ha

noncomputable def g57rho {N : ℕ} (α ϵ : ℝ) (j : Fin N) (x : Fin N × Bool) : ℝ :=
  bern (imabMeans α ϵ j x.1) x.2 / bern α x.2

lemma g57_imab_bern_pos {N : ℕ} {α ϵ : ℝ} (hα : 0 < α) (hϵ : 0 < ϵ) (h1 : α + ϵ < 1)
    (j a : Fin N) (b : Bool) : 0 < bern (imabMeans α ϵ j a) b := by
  unfold imabMeans; split_ifs <;> apply g57_bern_pos <;> linarith

lemma g57_rho_pos {N : ℕ} {α ϵ : ℝ} (hα : 0 < α) (hϵ : 0 < ϵ) (h1 : α + ϵ < 1)
    (j : Fin N) (x : Fin N × Bool) : 0 < g57rho α ϵ j x :=
  div_pos (g57_imab_bern_pos hα hϵ h1 j x.1 x.2) (g57_bern_pos hα (by linarith) _)

lemma g57_q_eq {N : ℕ} (A : MABAlg N) {α ϵ : ℝ} (hα : 0 < α) (hϵ : 0 < ϵ) (h1 : α + ϵ < 1)
    (j : Fin N) (s : ℕ) (h : Fin s → Fin N × Bool) :
    mabLaw A (imabMeans α ϵ j) s h = mabLaw A (fun _ => α) s h * ∏ t, g57rho α ϵ j (h t) := by
  unfold mabLaw g57rho
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro t _
  have := (g57_bern_pos hα (by linarith) (h t).2).ne'
  field_simp

lemma g57_law_nonneg {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (s : ℕ) (h : Fin s → Fin N × Bool) : 0 ≤ mabLaw A μ s h := by
  unfold mabLaw
  apply prod_nonneg
  intro t _
  apply mul_nonneg ((hA _ _).1 _)
  rcases (h t).2 with _ | _ <;> simp [bern] <;> linarith [hμ (h t).1]

lemma g57_A_le_one {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (t : ℕ) (h : Fin t → Fin N × Bool)
    (i : Fin N) : A t h i ≤ 1 := by
  rw [← (hA t h).2]
  exact single_le_sum (fun k _ => (hA t h).1 k) (mem_univ i)

lemma g57_armProb_nonneg {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ)
    (hμ : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1) (s : ℕ) (i : Fin N) : 0 ≤ armProb A μ s i :=
  sum_nonneg fun h _ => mul_nonneg (g57_law_nonneg A hA μ hμ s h) ((hA _ _).1 _)

lemma g57_armProb_sum {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (μ : Fin N → ℝ) (s : ℕ) :
    ∑ i, armProb A μ s i = 1 := by
  unfold armProb
  rw [sum_comm]
  simp_rw [← mul_sum, (hA _ _).2, mul_one]
  exact g57_law_sum A hA μ s

lemma g57_neglog (u : ℝ) (hu : 0 < u) : -Real.log u ≤ u⁻¹ - 1 := by
  rw [← Real.log_inv]; exact Real.log_le_sub_one_of_pos (inv_pos.mpr hu)

lemma g57_klv {N : ℕ} {α ϵ : ℝ} (hα : 0 < α) (hϵ : 0 < ϵ) (h1 : α + ϵ < 1) (j : Fin N) :
    ∑ b : Bool, bern α b * (-Real.log (g57rho α ϵ j (j, b))) ≤
      ϵ ^ 2 / ((α + ϵ) * (1 - α - ϵ)) := by
  rw [Fintype.sum_bool]
  simp only [g57rho, imabMeans, bern]
  have hq : 0 < 1 - (α + ϵ) := by linarith
  have h1' : 0 < 1 - α := by linarith
  have e1 := g57_neglog ((α + ϵ) / α) (by positivity)
  have e2 := g57_neglog ((1 - (α + ϵ)) / (1 - α)) (by positivity)
  calc α * -Real.log ((α + ϵ) / α) + (1 - α) * -Real.log ((1 - (α + ϵ)) / (1 - α))
      ≤ α * (((α + ϵ) / α)⁻¹ - 1) + (1 - α) * (((1 - (α + ϵ)) / (1 - α))⁻¹ - 1) := by
        gcongr
    _ = ϵ ^ 2 / ((α + ϵ) * (1 - α - ϵ)) := by
        have : (1 - α - ϵ) ≠ 0 := by linarith
        field_simp
        ring

lemma g57_chain {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) {α ϵ : ℝ} (hα : 0 < α) (hϵ : 0 < ϵ)
    (h1 : α + ϵ < 1) (j : Fin N) (s : ℕ) :
    ∑ h : Fin s → Fin N × Bool, mabLaw A (fun _ => α) s h *
        (-Real.log (∏ t, g57rho α ϵ j (h t))) =
      ∑ t ∈ range s, armProb A (fun _ => α) t j *
        ∑ b : Bool, bern α b * (-Real.log (g57rho α ϵ j (j, b))) := by
  have hne : ∀ h : Fin s → Fin N × Bool, ∀ t ∈ (univ : Finset (Fin s)),
      g57rho α ϵ j (h t) ≠ 0 := fun h t _ => (g57_rho_pos hα hϵ h1 j _).ne'
  have hL : ∑ h : Fin s → Fin N × Bool, mabLaw A (fun _ => α) s h *
        (-Real.log (∏ t, g57rho α ϵ j (h t))) =
      ∑ t : Fin s, ∑ h : Fin s → Fin N × Bool, mabLaw A (fun _ => α) s h *
        (-Real.log (g57rho α ϵ j (h t))) := by
    simp_rw [fun h => Real.log_prod (hne h), ← sum_neg_distrib, mul_sum]
    rw [sum_comm]
  rw [hL, ← Fin.sum_univ_eq_sum_range (fun t => armProb A (fun _ => α) t j *
        ∑ b : Bool, bern α b * (-Real.log (g57rho α ϵ j (j, b)))) s]
  apply sum_congr rfl
  intro t _
  rw [g57_marg A hA (fun _ => α) s t (fun x => -Real.log (g57rho α ϵ j x))]
  unfold armProb
  rw [sum_mul]
  apply sum_congr rfl
  intro h _
  rw [mul_assoc]
  congr 1
  rw [Fintype.sum_prod_type, sum_eq_single j]
  · rw [mul_sum]
    apply sum_congr rfl
    intro b _
    ring
  · intro a _ ha
    apply sum_eq_zero
    intro b _
    have : g57rho α ϵ j (a, b) = 1 := by
      unfold g57rho imabMeans
      simp only [if_neg ha]
      exact div_self (g57_bern_pos hα (by linarith) b).ne'
    rw [this, Real.log_one]
    ring
  · intro h; exact absurd (mem_univ j) h

theorem g57_core {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) {α ϵ : ℝ} (hα : 0 < α)
    (hϵ : 0 < ϵ) (h1 : α + ϵ < 1) (j : Fin N) (s : ℕ) :
    (armProb A (imabMeans α ϵ j) s j - armProb A (fun _ => α) s j) ^ 2 ≤
      ϵ ^ 2 / ((α + ϵ) * (1 - α - ϵ)) * ∑ t ∈ range s, armProb A (fun _ => α) t j := by
  have hμ0 : ∀ i : Fin N, 0 ≤ (fun _ => α) i ∧ (fun _ => α) i ≤ 1 := fun _ => ⟨hα.le, by simp; linarith⟩
  have tv := g57_tv (mabLaw A (fun _ => α) s) (fun h => ∏ t, g57rho α ϵ j (h t))
    (fun h => A s h j) (g57_law_nonneg A hA _ hμ0 s)
    (fun h => prod_pos fun t _ => g57_rho_pos hα hϵ h1 j _) (fun h => (hA s h).1 j)
    (fun h => g57_A_le_one A hA s h j) (g57_law_sum A hA _ s)
    (by simp_rw [← g57_q_eq A hα hϵ h1 j s]; exact g57_law_sum A hA _ s)
  have ex : armProb A (imabMeans α ϵ j) s j =
      ∑ h, mabLaw A (fun _ => α) s h * (∏ t, g57rho α ϵ j (h t)) * A s h j := by
    unfold armProb
    simp_rw [g57_q_eq A hα hϵ h1 j s]
  rw [ex]
  unfold armProb
  refine tv.trans ?_
  rw [g57_chain A hA hα hϵ h1 j s, mul_sum]
  apply sum_le_sum
  intro t _
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right (g57_klv hα hϵ h1 j)
  exact g57_armProb_nonneg A hA _ hμ0 t j

lemma g57_inner_aux {N : ℕ} (w : Fin N → ℝ) (hw : ∑ i, w i = 1) (ϵ : ℝ) (j : Fin N)
    (g : Fin N → Bool → ℝ) (hg : ∀ a, ∑ b, g a b = 1) (φ : Fin N → ℝ)
    (hφ : ∀ a, φ a = ϵ - ϵ * if a = j then 1 else 0) :
    ∑ x : Fin N × Bool, w x.1 * g x.1 x.2 * φ x.1 = ϵ - ϵ * w j := by
  rw [Fintype.sum_prod_type]
  have : ∀ a, ∑ b, w a * g a b * φ a = ϵ * w a - (if a = j then ϵ * w a else 0) := by
    intro a
    rw [← sum_mul, ← mul_sum, hg a, hφ a]
    split_ifs <;> ring
  simp_rw [this]
  rw [sum_sub_distrib, ← mul_sum, hw, sum_ite_eq' univ j]
  simp

lemma g57_regret_eq {N : ℕ} (A : MABAlg N) (hA : IsMABAlg A) (α ϵ : ℝ) (j : Fin N) (T : ℕ) :
    ∑ h : Fin T → Fin N × Bool, mabLaw A (imabMeans α ϵ j) T h *
        ∑ t : Fin T, (imabMeans α ϵ j j - imabMeans α ϵ j (h t).1) =
      ∑ t ∈ range T, (ϵ - ϵ * armProb A (imabMeans α ϵ j) t j) := by
  simp_rw [mul_sum]
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range (fun t => ϵ - ϵ * armProb A (imabMeans α ϵ j) t j) T]
  apply sum_congr rfl
  intro t _
  rw [g57_marg A hA (imabMeans α ϵ j) T t (fun x => imabMeans α ϵ j j - imabMeans α ϵ j x.1)]
  have hφ : ∀ a : Fin N, imabMeans α ϵ j j - imabMeans α ϵ j a =
      ϵ - ϵ * (if a = j then 1 else 0) := by
    intro a
    unfold imabMeans
    by_cases h : a = j <;> simp [h]
  have inner : ∀ h : Fin t → Fin N × Bool,
      ∑ x : Fin N × Bool, A t h x.1 * bern (imabMeans α ϵ j x.1) x.2 *
        (imabMeans α ϵ j j - imabMeans α ϵ j x.1) = ϵ - ϵ * A t h j :=
    fun h => g57_inner_aux (A t h) (hA t h).2 ϵ j (fun a b => bern (imabMeans α ϵ j a) b)
      (fun a => g57_bern_sum _) _ hφ
  simp_rw [inner]
  have e : ∀ h' : Fin t → Fin N × Bool, mabLaw A (imabMeans α ϵ j) t h' * (ϵ - ϵ * A t h' j) =
      ϵ * mabLaw A (imabMeans α ϵ j) t h' - ϵ * (mabLaw A (imabMeans α ϵ j) t h' * A t h' j) :=
    fun h' => by ring
  rw [sum_congr rfl (fun h' _ => e h'), sum_sub_distrib, ← mul_sum, ← mul_sum,
    g57_law_sum A hA _ t]
  unfold armProb
  ring

theorem lemma_5_1_core (N : ℕ) (hN : 2 ≤ N) (α : ℝ) (hα : 0 < α) (T : ℕ) (hT : 1 ≤ T)
    (hαϵ : 2 * α + epsMAB N α T ≤ 1) (A : MABAlg N) (hA : IsMABAlg A) :
    epsMAB N α T * T / 6 ≤ regretIMAB A α (epsMAB N α T) T := by
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hϵ : 0 < epsMAB N α T := by
    unfold epsMAB
    apply mul_pos (by norm_num)
    apply Real.sqrt_pos.mpr
    positivity
  have hϵ2 : epsMAB N α T ^ 2 = 1/10000 * (N * α / T) := by
    unfold epsMAB
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  generalize epsMAB N α T = ϵ at hϵ hϵ2 hαϵ ⊢
  have h1 : α + ϵ < 1 := by linarith
  have hden : 0 < (α + ϵ) * (1 - α - ϵ) := mul_pos (by linarith) (by linarith)
  set c := ϵ ^ 2 / ((α + ϵ) * (1 - α - ϵ)) with hc
  have hc0 : 0 ≤ c := div_nonneg (sq_nonneg _) hden.le
  have key : α ≤ 2 * ((α + ϵ) * (1 - α - ϵ)) := by
    nlinarith [mul_nonneg hϵ.le (show 0 ≤ 1 - 2*α - ϵ by linarith),
      mul_nonneg hα.le (show 0 ≤ 1 - 2*α by linarith)]
  have hcle : c ≤ 2 * ϵ ^ 2 / α := by
    rw [hc, div_le_div_iff₀ hden hα]
    nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg ϵ)]
  have hcT : c * T ≤ 2 * N / 10000 := by
    calc c * T ≤ 2 * ϵ ^ 2 / α * T := mul_le_mul_of_nonneg_right hcle (by positivity)
      _ = 2 * N / 10000 := by rw [hϵ2]; field_simp
  have hx : ∀ (j : Fin N) (t : ℕ), armProb A (imabMeans α ϵ j) t j ≤
      armProb A (fun _ => α) t j + 1/20 + 5 * c * ∑ u ∈ range t, armProb A (fun _ => α) u j := by
    intro j t
    have := g57_core A hA hα hϵ h1 j t
    nlinarith [sq_nonneg (armProb A (imabMeans α ϵ j) t j - armProb A (fun _ => α) t j - 1/10)]
  have hsumx : ∀ t ≤ T, ∑ j, armProb A (imabMeans α ϵ j) t j ≤ 5 * N / 6 := by
    intro t ht
    have hY : ∑ j : Fin N, ∑ u ∈ range t, armProb A (fun _ => α) u j = t := by
      rw [sum_comm]
      simp_rw [g57_armProb_sum A hA]
      simp
    have htT : (t : ℝ) ≤ T := by exact_mod_cast ht
    calc ∑ j, armProb A (imabMeans α ϵ j) t j
        ≤ ∑ j, (armProb A (fun _ => α) t j + 1/20 +
            5 * c * ∑ u ∈ range t, armProb A (fun _ => α) u j) := sum_le_sum fun j _ => hx j t
      _ = 1 + N / 20 + 5 * c * t := by
        rw [sum_add_distrib, sum_add_distrib, g57_armProb_sum A hA, ← mul_sum, hY]
        simp
        ring
      _ ≤ 5 * N / 6 := by nlinarith [mul_le_mul_of_nonneg_left htT hc0]
  unfold regretIMAB
  rw [sum_congr rfl (fun j _ => g57_regret_eq A hA α ϵ j T), sum_comm]
  have hinner : ∀ t ∈ range T, N * ϵ / 6 ≤
      ∑ j : Fin N, (ϵ - ϵ * armProb A (imabMeans α ϵ j) t j) := by
    intro t ht
    rw [sum_sub_distrib, ← mul_sum]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [hsumx t (le_of_lt (mem_range.mp ht)), hϵ]
  have := sum_le_sum hinner
  simp only [sum_const, card_range, nsmul_eq_mul] at this
  have hN0 : (0:ℝ) < N := by linarith
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hN0]
  have e : ϵ * T / 6 * N = T * (N * ϵ / 6) := by ring
  linarith

theorem lemma_E_2_core (N : ℕ) (hN : 12 ≤ N) (α ϵ : ℝ) (hα : 0 < α) (hϵ : 0 < ϵ)
    (hϵ4 : ϵ ≤ 1 / 4) (hαϵ : 2 * α + ϵ ≤ 1)
    (A : MABAlg N) (hA : IsMABAlg A) (s : ℕ)
    (hs : (s : ℝ) + 1 ≤ (N : ℝ) * α / (60 * ϵ ^ 2)) :
    ∃ J : Finset (Fin N), (N : ℝ) / 3 ≤ J.card ∧
      ∀ j ∈ J, armProb A (imabMeans α ϵ j) s j ≤ 1 / 2 := by
  have hNr : (12:ℝ) ≤ N := by exact_mod_cast hN
  have h1 : α + ϵ < 1 := by linarith
  have hden : 0 < (α + ϵ) * (1 - α - ϵ) := mul_pos (by linarith) (by linarith)
  set c := ϵ ^ 2 / ((α + ϵ) * (1 - α - ϵ)) with hc
  have hc0 : 0 ≤ c := div_nonneg (sq_nonneg _) hden.le
  have key : 3 * α ≤ 8 * ((α + ϵ) * (1 - α - ϵ)) := by
    have : 3/8 ≤ 1 - α - ϵ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ α + ϵ)]
  have hcle : c ≤ 8 * ϵ ^ 2 / (3 * α) := by
    rw [hc, div_le_div_iff₀ hden (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg ϵ)]
  have hs' : ((s : ℝ) + 1) * (60 * ϵ ^ 2) ≤ N * α := by
    rwa [le_div_iff₀ (by positivity)] at hs
  have hcs : c * s ≤ 2 * N / 45 := by
    calc c * s ≤ 8 * ϵ ^ 2 / (3 * α) * s := mul_le_mul_of_nonneg_right hcle (by positivity)
      _ = 8 * (ϵ ^ 2 * s) / (3 * α) := by ring
      _ ≤ 8 * (N * α / 60) / (3 * α) := by
          gcongr
          nlinarith [sq_nonneg ϵ]
      _ = 2 * N / 45 := by field_simp; ring
  have hμ0 : ∀ i : Fin N, 0 ≤ (fun _ => α) i ∧ (fun _ => α) i ≤ 1 :=
    fun _ => ⟨hα.le, by simp; linarith⟩
  set y : Fin N → ℝ := fun j => armProb A (fun _ => α) s j with hy
  set Y : Fin N → ℝ := fun j => ∑ u ∈ range s, armProb A (fun _ => α) u j with hYd
  set z : Fin N → ℝ := fun j => N * y j + 45 / 2 * c * Y j with hz
  have hy0 : ∀ j, 0 ≤ y j := fun j => g57_armProb_nonneg A hA _ hμ0 s j
  have hY0 : ∀ j, 0 ≤ Y j := fun j => sum_nonneg fun u _ => g57_armProb_nonneg A hA _ hμ0 u j
  have hz0 : ∀ j, 0 ≤ z j := fun j => by
    simp only [hz]; have := hy0 j; have := hY0 j; positivity
  have hYs : ∑ j, Y j = s := by
    simp only [hYd]
    rw [sum_comm]
    simp_rw [g57_armProb_sum A hA]
    simp
  have hzs : ∑ j, z j ≤ 2 * N := by
    simp only [hz]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hYs]
    simp only [hy, g57_armProb_sum A hA]
    nlinarith
  refine ⟨univ.filter (fun j => z j ≤ 3), ?_, ?_⟩
  · have hc1 := card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
      (p := fun j => z j ≤ 3)
    simp only [card_univ, Fintype.card_fin] at hc1
    have hbad : 3 * ((univ.filter (fun j => ¬ z j ≤ 3)).card : ℝ) ≤ 2 * N := by
      calc 3 * ((univ.filter (fun j => ¬ z j ≤ 3)).card : ℝ)
          = ∑ j ∈ univ.filter (fun j => ¬ z j ≤ 3), (3:ℝ) := by simp; ring
        _ ≤ ∑ j ∈ univ.filter (fun j => ¬ z j ≤ 3), z j := by
            apply sum_le_sum
            intro j hj
            simp only [mem_filter] at hj
            linarith [hj.2]
        _ ≤ ∑ j, z j := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun j _ _ => hz0 j)
        _ ≤ 2 * N := hzs
    have : ((univ.filter (fun j => z j ≤ 3)).card : ℝ) +
        ((univ.filter (fun j => ¬ z j ≤ 3)).card : ℝ) = N := by exact_mod_cast hc1
    linarith
  · intro j hj
    simp only [mem_filter] at hj
    have hzj := hj.2
    simp only [hz] at hzj
    have hcore := g57_core A hA hα hϵ h1 j s
    change (armProb A (imabMeans α ϵ j) s j - y j) ^ 2 ≤ c * Y j at hcore
    set W := 45 / 2 * c * Y j with hW
    have hW0 : 0 ≤ W := by have := hY0 j; positivity
    have hcY : c * Y j = 2 * W / 45 := by rw [hW]; ring
    have hyj : 12 * y j ≤ 3 - W := by nlinarith [hy0 j]
    have hW3 : W ≤ 3 := by nlinarith [hy0 j]
    by_contra hx
    push Not at hx
    have hd : 1/4 + W/12 < armProb A (imabMeans α ϵ j) s j - y j := by linarith
    have hsq : (1/4 + W/12) ^ 2 < (armProb A (imabMeans α ϵ j) s j - y j) ^ 2 := by
      have : 0 ≤ 1/4 + W/12 := by linarith
      nlinarith
    nlinarith

end MNLBandit.LowerBound

open MNLBandit.LowerBound


theorem solution (N : ℕ) (hN : 12 ≤ N) (α ϵ : ℝ) (hα : 0 < α) (hϵ : 0 < ϵ)
    (hϵ4 : ϵ ≤ 1 / 4) (hαϵ : 2 * α + ϵ ≤ 1)
    (A : MABAlg N) (hA : IsMABAlg A) (s : ℕ)
    (hs : (s : ℝ) + 1 ≤ (N : ℝ) * α / (60 * ϵ ^ 2)) :
    ∃ J : Finset (Fin N), (N : ℝ) / 3 ≤ J.card ∧
      ∀ j ∈ J, armProb A (imabMeans α ϵ j) s j ≤ 1 / 2 := by
  exact lemma_E_2_core N hN α ϵ hα hϵ hϵ4 hαϵ A hA s hs
