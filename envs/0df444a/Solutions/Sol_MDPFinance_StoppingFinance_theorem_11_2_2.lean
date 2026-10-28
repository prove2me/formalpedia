-- Prove2me | solution 1 for MDPFinance.StoppingFinance.theorem_11_2_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:03:46.794183+00:00
-- url     : https://prove2.me/submissions/2057e94f-e565-4239-8adf-3471b3acafc5

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_CreditModel

open MeasureTheory

namespace S99Credit
open MDPFinance.StoppingFinance

variable (M : BayesCreditModel)

noncomputable def I (a b : ℕ) : ℝ := ∫ p, p ^ a * (1 - p) ^ b ∂M.mu0

lemma ae_Icc : ∀ᵐ p ∂M.mu0, p ∈ Set.Icc (0:ℝ) 1 := by
  rw [ae_iff]
  convert M.mu0_supp using 2
  ext p
  simp only [Set.mem_Icc, Set.mem_setOf_eq, not_and_or, not_le]

lemma integ (a b : ℕ) : Integrable (fun p : ℝ => p ^ a * (1 - p) ^ b) M.mu0 := by
  have := M.mu0_prob
  refine Integrable.of_bound (by fun_prop : Continuous fun p : ℝ => p ^ a * (1 - p) ^ b).aestronglyMeasurable 1 ?_
  filter_upwards [ae_Icc M] with p hp
  have h0 := hp.1
  have h1 : 0 ≤ 1 - p := by linarith [hp.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_one₀ (pow_le_one₀ hp.1 hp.2) (by positivity)
    (pow_le_one₀ h1 (by linarith [hp.1]))

lemma I_pos (a b : ℕ) : 0 < I M a b := by
  unfold I
  rw [integral_pos_iff_support_of_nonneg_ae _ (integ M a b)]
  · refine lt_of_lt_of_le M.mu0_nondeg (measure_mono fun p hp => ?_)
    simp only [Function.mem_support]
    have h1 := hp.1
    have h2 : 0 < 1 - p := by linarith [hp.2]
    positivity
  · filter_upwards [ae_Icc M] with p hp
    have := hp.1
    have : 0 ≤ 1 - p := by linarith [hp.2]
    simp only [Pi.zero_apply]
    positivity

lemma I_rec (a b : ℕ) : I M a (b + 1) = I M a b - I M (a + 1) b := by
  unfold I
  rw [← integral_sub (integ M a b) (integ M (a + 1) b)]
  congr 1; ext p; ring

lemma I_cs (a b : ℕ) : I M (a + 1) b ^ 2 ≤ I M (a + 1 + 1) b * I M a b := by
  have hA := I_pos M a b
  have key : ∫ p, (I M a b ^ 2 * (p ^ (a + 1 + 1) * (1 - p) ^ b)
      - 2 * I M a b * I M (a + 1) b * (p ^ (a + 1) * (1 - p) ^ b))
      + I M (a + 1) b ^ 2 * (p ^ a * (1 - p) ^ b) ∂M.mu0
      = I M a b ^ 2 * I M (a + 1 + 1) b - 2 * I M a b * I M (a + 1) b * I M (a + 1) b
        + I M (a + 1) b ^ 2 * I M a b := by
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul]
    · rfl
    · exact (integ M _ _).const_mul _
    · exact (integ M _ _).const_mul _
    · exact ((integ M _ _).const_mul _).sub ((integ M _ _).const_mul _)
    · exact (integ M _ _).const_mul _
  have hnn : 0 ≤ ∫ p, (I M a b ^ 2 * (p ^ (a + 1 + 1) * (1 - p) ^ b)
      - 2 * I M a b * I M (a + 1) b * (p ^ (a + 1) * (1 - p) ^ b))
      + I M (a + 1) b ^ 2 * (p ^ a * (1 - p) ^ b) ∂M.mu0 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_Icc M] with p hp
    have h0 := hp.1
    have h1 : 0 ≤ 1 - p := by linarith [hp.2]
    have : (I M a b ^ 2 * (p ^ (a + 1 + 1) * (1 - p) ^ b)
      - 2 * I M a b * I M (a + 1) b * (p ^ (a + 1) * (1 - p) ^ b))
      + I M (a + 1) b ^ 2 * (p ^ a * (1 - p) ^ b)
        = (p * I M a b - I M (a + 1) b) ^ 2 * (p ^ a * (1 - p) ^ b) := by ring
    simp only [Pi.zero_apply]
    rw [this]; positivity
  rw [key] at hnn
  have h2 : 0 ≤ I M a b * (I M (a + 1 + 1) b * I M a b - I M (a + 1) b ^ 2) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left hA).mp h2
  linarith

noncomputable def r (s f : ℕ) : ℝ := I M (s + 1) f / I M s f

lemma r_pos (s f : ℕ) : 0 < r M s f := div_pos (I_pos M _ _) (I_pos M _ _)

lemma r_lt_one (s f : ℕ) : r M s f < 1 := by
  unfold r
  rw [div_lt_one (I_pos M _ _)]
  have := I_pos M s (f + 1)
  rw [I_rec] at this
  linarith

lemma r_le_succ_s (s f : ℕ) : r M s f ≤ r M (s + 1) f := by
  unfold r
  rw [div_le_div_iff₀ (I_pos M _ _) (I_pos M _ _)]
  nlinarith [I_cs M s f]

lemma r_succ_f_le (s f : ℕ) : r M s (f + 1) ≤ r M s f := by
  unfold r
  rw [div_le_div_iff₀ (I_pos M _ _) (I_pos M _ _), I_rec, I_rec]
  nlinarith [I_cs M s f]

lemma r_mono {s f s' f' : ℕ} (hs : s ≤ s') (hf : f' ≤ f) : r M s f ≤ r M s' f' := by
  have h1 : r M s f ≤ r M s' f :=
    (monotone_nat_of_le_succ (fun t => r_le_succ_s M t f)) hs
  have h2 : r M s' f ≤ r M s' f' :=
    (antitone_nat_of_succ_le (fun t => r_succ_f_le M s' t)) hf
  linarith

lemma q_eq (s n : ℕ) : M.q s n = r M s (n - s) := rfl

lemma q_pos (s n : ℕ) : 0 < M.q s n := by rw [q_eq]; exact r_pos M _ _
lemma q_lt_one (s n : ℕ) : M.q s n < 1 := by rw [q_eq]; exact r_lt_one M _ _

lemma q_mono {s n s' n' : ℕ} (hs : s ≤ s') (hf : n' - s' ≤ n - s) : M.q s n ≤ M.q s' n' := by
  rw [q_eq, q_eq]; exact r_mono M hs hf

lemma c_mono {s n s' n' : ℕ} (hs : s ≤ s') (hf : n' - s' ≤ n - s) : M.c s n ≤ M.c s' n' := by
  unfold BayesCreditModel.c
  have := q_mono M hs hf
  have := M.K1_pos; have := M.K0_neg
  nlinarith

def Mono (k : ℕ) : Prop := ∀ s n s' n' : ℕ, s ≤ n → s' ≤ n' → s ≤ s' → n' - s' ≤ n - s →
  M.J k s n ≤ M.J k s' n'

lemma cbar_mono (k : ℕ) (hJ : Mono M (k - 1)) {s n s' n' : ℕ} (hsn : s ≤ n) (hsn' : s' ≤ n')
    (hs : s ≤ s') (hf : n' - s' ≤ n - s) : M.cbar k s n ≤ M.cbar k s' n' := by
  unfold BayesCreditModel.cbar
  have hq := q_mono M hs hf
  have hq0 := q_pos M s n
  have hq1 := q_lt_one M s' n'
  have hc := c_mono M hs hf
  have hβ : 0 < M.beta := M.beta_mem.1
  have hba : M.J (k - 1) s (n + 1) ≤ M.J (k - 1) (s + 1) (n + 1) :=
    hJ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  have haa : M.J (k - 1) (s + 1) (n + 1) ≤ M.J (k - 1) (s' + 1) (n' + 1) :=
    hJ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hbb : M.J (k - 1) s (n + 1) ≤ M.J (k - 1) s' (n' + 1) :=
    hJ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
  set a := M.J (k - 1) (s + 1) (n + 1)
  set b := M.J (k - 1) s (n + 1)
  set a' := M.J (k - 1) (s' + 1) (n' + 1)
  set b' := M.J (k - 1) s' (n' + 1)
  have h1 : M.q s n * (a - b) ≤ M.q s' n' * (a - b) :=
    mul_le_mul_of_nonneg_right hq (by linarith)
  have h2 : 0 ≤ M.q s' n' * (a' - a) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ (1 - M.q s' n') * (b' - b) := mul_nonneg (by linarith) (by linarith)
  have inner : M.q s n * a + (1 - M.q s n) * b ≤ M.q s' n' * a' + (1 - M.q s' n') * b' := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left inner hβ.le]

lemma J_succ (k s n : ℕ) : M.J (k + 1) s n = max 0 (M.cbar (k + 1) s n) := rfl

lemma J_zero (s n : ℕ) : M.J 0 s n = 0 := rfl

lemma J_mono (k : ℕ) : Mono M k := by
  induction k with
  | zero => intro s n s' n' _ _ _ _; simp [J_zero]
  | succ k ih =>
    intro s n s' n' h1 h2 h3 h4
    rw [J_succ, J_succ]
    exact max_le_max le_rfl (cbar_mono M (k + 1) (by simpa using ih) h1 h2 h3 h4)

lemma J_le_succ (k : ℕ) : ∀ s n, M.J k s n ≤ M.J (k + 1) s n := by
  induction k with
  | zero => intro s n; rw [J_zero, J_succ]; exact le_max_left _ _
  | succ k ih =>
    intro s n
    rw [J_succ, J_succ M (k + 1)]
    refine max_le_max le_rfl ?_
    unfold BayesCreditModel.cbar
    simp only [Nat.add_sub_cancel]
    have hq0 := q_pos M s n
    have hq1 := q_lt_one M s n
    have hβ : 0 < M.beta := M.beta_mem.1
    have e1 := ih (s + 1) (n + 1)
    have e2 := ih s (n + 1)
    have : M.beta * M.q s n * M.J k (s + 1) (n + 1) ≤ M.beta * M.q s n * M.J (k + 1) (s + 1) (n + 1) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have : M.beta * (1 - M.q s n) * M.J k s (n + 1) ≤ M.beta * (1 - M.q s n) * M.J (k + 1) s (n + 1) :=
      mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ.le (by linarith))
    linarith

lemma J_le_of_le {j k : ℕ} (h : j ≤ k) (s n : ℕ) : M.J j s n ≤ M.J k s n :=
  (monotone_nat_of_le_succ (fun t => J_le_succ M t s n)) h

lemma cbar_le_of_le {j k : ℕ} (h : j ≤ k) (s n : ℕ) : M.cbar j s n ≤ M.cbar k s n := by
  unfold BayesCreditModel.cbar
  have hq0 := q_pos M s n
  have hq1 := q_lt_one M s n
  have hβ : 0 < M.beta := M.beta_mem.1
  have e1 := J_le_of_le M (show j - 1 ≤ k - 1 by omega) (s + 1) (n + 1)
  have e2 := J_le_of_le M (show j - 1 ≤ k - 1 by omega) s (n + 1)
  have := mul_le_mul_of_nonneg_left e1 (show 0 ≤ M.beta * M.q s n by positivity)
  have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hβ.le (show 0 ≤ 1 - M.q s n by linarith))
  linarith

end S99Credit

open MDPFinance.StoppingFinance in
theorem solution (M : MDPFinance.StoppingFinance.BayesCreditModel) (N : ℕ) :
    (∀ (k : ℕ) (s n s' n' : ℕ), s ≤ n → s' ≤ n' →
      MDPFinance.StoppingFinance.BayesCreditModel.stateLe (s, n) (s', n') → M.J k s n ≤ M.J k s' n') ∧
    (∀ (j k : ℕ), j ≤ k → ∀ s n : ℕ, s ≤ n → M.J j s n ≤ M.J k s n) ∧
    (∃ tstar : ℕ → ℕ,
      (∀ (j k : ℕ), 1 ≤ j → j ≤ k → k ≤ N → tstar k ≤ tstar j) ∧
      (∀ (k s : ℕ), 1 ≤ k → k ≤ N → s ≤ N - k → (M.cbar k s (N - k) < 0 ↔ s < tstar k)) ∧
      ∀ (k s : ℕ), 1 ≤ k → k ≤ N → s ≤ N - k →
        (if s < tstar k then 0 else M.cbar k s (N - k)) = M.J k s (N - k)) := by
  classical
  have cm : ∀ k : ℕ, ∀ {s n s' n' : ℕ}, s ≤ n → s' ≤ n' → s ≤ s' → n' - s' ≤ n - s →
      M.cbar k s n ≤ M.cbar k s' n' := fun k => S99Credit.cbar_mono M k (S99Credit.J_mono M _)
  refine ⟨?_, ?_, ?_⟩
  · intro k s n s' n' h1 h2 h3
    obtain ⟨ha, hb⟩ := h3
    simp only at ha hb
    exact S99Credit.J_mono M k s n s' n' h1 h2 ha (by omega)
  · intro j k hjk s n _
    exact S99Credit.J_le_of_le M hjk s n
  · let tstar : ℕ → ℕ := fun k =>
      if h : ∃ s, s ≤ N - k ∧ 0 ≤ M.cbar k s (N - k) then Nat.find h else N - k + 1
    have tle : ∀ k, tstar k ≤ N - k + 1 := by
      intro k
      simp only [tstar]
      split_ifs with h
      · have := Nat.find_spec h; have := Nat.find_min' h this; omega
      · exact le_rfl
    have iff : ∀ k s, s ≤ N - k → (M.cbar k s (N - k) < 0 ↔ s < tstar k) := by
      intro k s hs
      simp only [tstar]
      split_ifs with h
      · rw [Nat.lt_find_iff]
        constructor
        · intro hc m hm hp
          have := cm k (show m ≤ N - k by omega) (show s ≤ N - k by omega) hm (by omega)
          linarith [hp.2]
        · intro hall
          by_contra hc
          exact hall s le_rfl ⟨hs, le_of_not_gt hc⟩
      · constructor
        · intro _; omega
        · intro _
          by_contra hc
          exact h ⟨s, hs, le_of_not_gt hc⟩
    refine ⟨tstar, ?_, fun k s _ _ hs => iff k s hs, ?_⟩
    · intro j k hj hjk hkN
      by_contra hlt
      push Not at hlt
      set t := tstar j
      have ht : t ≤ N - k := by have := tle k; omega
      have h1 := (iff k t ht).2 hlt
      have h2 := S99Credit.cbar_le_of_le M hjk t (N - j)
      have h3 := cm k (show t ≤ N - j by omega) (show t ≤ N - k by omega) le_rfl (by omega)
      have h4 := (iff j t (by omega)).1 (by linarith)
      exact lt_irrefl _ h4
    · intro k s hk _ hs
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [S99Credit.J_succ]
      have := iff (k' + 1) s hs
      split_ifs with h
      · rw [max_eq_left (le_of_lt (this.2 h))]
      · rw [max_eq_right (le_of_not_gt (fun h' => h (this.1 h')))]
