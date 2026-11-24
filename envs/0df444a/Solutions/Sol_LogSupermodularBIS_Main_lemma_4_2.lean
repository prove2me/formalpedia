-- Prove2me | solution 1 for LogSupermodularBIS.Main.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T21:02:30.908746+00:00
-- url     : https://prove2.me/submissions/40ac5864-cb97-46de-b5b5-ae9206f4768e

import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

lemma logit_eq (u : ℝ) : logit u = Real.log u - Real.log (1 - u) := by
  unfold logit
  by_cases h0 : u = 0
  · simp [h0]
  by_cases h1 : 1 - u = 0
  · have : u = 1 := by linarith
    simp [this]
  · exact Real.log_div h0 h1

lemma logit_ii (a b : ℝ) : IntervalIntegrable logit volume a b := by
  have h1 : IntervalIntegrable Real.log volume a b := intervalIntegral.intervalIntegrable_log'
  have h2 : IntervalIntegrable (fun x => Real.log (1 - x)) volume a b := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 1 - a) (b := 1 - b)).comp_sub_left 1
    simpa using this
  have := h1.sub h2
  refine this.congr ?_
  exact fun u _ => (logit_eq u).symm

lemma logit_ftc (l r : ℝ) (h0 : 0 ≤ l) (hlr : l ≤ r) (h1 : r ≤ 1) :
    ∫ u in l..r, logit u = H l - H r := by
  have key : ∫ u in l..r, logit u = (fun x => -Real.binEntropy x) r - (fun x => -Real.binEntropy x) l := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := fun x => -Real.binEntropy x) hlr ?_ ?_ (logit_ii l r)
    · exact (Real.binEntropy_continuous.neg).continuousOn
    · intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (lt_of_le_of_lt h0 hx.1)
      have hx1 : x ≠ 1 := ne_of_lt (lt_of_lt_of_le hx.2 h1)
      have := (Real.hasDerivAt_binEntropy hx0 hx1).neg
      have e : Real.log x - Real.log (1 - x) = -(Real.log (1 - x) - Real.log x) := by ring
      rw [logit_eq, e]
      exact this.hasDerivWithinAt
  rw [key]; simp only [H]; ring


lemma int_mono (f g : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hg : IntervalIntegrable g volume l r) (h : ∀ x ∈ Set.Ioo l r, f x ≤ g x) :
    ∫ x in l..r, f x ≤ ∫ x in l..r, g x := by
  rw [intervalIntegral.integral_of_le hlr, intervalIntegral.integral_of_le hlr,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_on (hf.1.mono_set Set.Ioo_subset_Ioc_self)
    (hg.1.mono_set Set.Ioo_subset_Ioc_self) measurableSet_Ioo h

lemma L_left (f : ℝ → ℝ) (l r K c : ℝ) (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hK : ∀ x ∈ Set.Ioo l r, f x ≤ K) (hc : c ≤ K) (hint : ∫ x in l..r, f x = c * (r - l)) :
    ∫ x in l..r, |f x - c| ≤ 2 * ((r - l) * K - c * (r - l)) := by
  have hg : IntervalIntegrable (fun x => (2 * K - c) - f x) volume l r :=
    intervalIntegrable_const.sub hf
  have h1 := int_mono (fun x => |f x - c|) (fun x => (2 * K - c) - f x) l r hlr
    (hf.sub intervalIntegrable_const).abs hg (by
      intro x hx
      have := hK x hx
      rw [abs_le]; constructor <;> linarith)
  have h2 : ∫ x in l..r, ((2 * K - c) - f x) = (r - l) * (2 * K - c) - c * (r - l) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hf, hint]
    simp; ring
  rw [h2] at h1
  linarith

lemma L_right (f : ℝ → ℝ) (l r K c : ℝ) (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hK : ∀ x ∈ Set.Ioo l r, K ≤ f x) (hc : K ≤ c) (hint : ∫ x in l..r, f x = c * (r - l)) :
    ∫ x in l..r, |f x - c| ≤ 2 * ((c - K) * (r - l)) := by
  have hg : IntervalIntegrable (fun x => f x + (c - 2 * K)) volume l r :=
    hf.add intervalIntegrable_const
  have h1 := int_mono (fun x => |f x - c|) (fun x => f x + (c - 2 * K)) l r hlr
    (hf.sub intervalIntegrable_const).abs hg (by
      intro x hx
      have := hK x hx
      rw [abs_le]; constructor <;> linarith)
  have h2 : ∫ x in l..r, (f x + (c - 2 * K)) = c * (r - l) + (r - l) * (c - 2 * K) := by
    rw [intervalIntegral.integral_add hf intervalIntegrable_const, hint]
    simp; ring
  rw [h2] at h1
  nlinarith

lemma L_mid (f : ℝ → ℝ) (l r K K' c : ℝ) (hlr : l ≤ r) (hf : IntervalIntegrable f volume l r)
    (hK : ∀ x ∈ Set.Ioo l r, f x ≤ K) (hK' : ∀ x ∈ Set.Ioo l r, K' ≤ f x) (hc : c ≤ K)
    (hc' : K' ≤ c) :
    ∫ x in l..r, |f x - c| ≤ (r - l) * (K - K') := by
  have h1 := int_mono (fun x => |f x - c|) (fun _ => K - K') l r hlr
    (hf.sub intervalIntegrable_const).abs intervalIntegrable_const (by
      intro x hx
      have := hK x hx
      have := hK' x hx
      rw [abs_le]; constructor <;> linarith)
  simp at h1; linarith

lemma logit_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) : logit u ≤ logit v := by
  rw [logit_eq, logit_eq]
  have := Real.log_le_log hu huv
  have := Real.log_le_log (by linarith : 0 < 1 - v) (by linarith : 1 - v ≤ 1 - u)
  linarith

lemma logit_one_sub (u : ℝ) : logit (1 - u) = - logit u := by
  rw [logit_eq, logit_eq]; simp

lemma logit_inv (M : ℝ) (hM : 2 ≤ M) : logit (1 / M) = - Real.log (M - 1) := by
  have h0 : 0 < M := by linarith
  have h1 : 0 < M - 1 := by linarith
  rw [logit_eq]
  have : 1 - 1 / M = (M - 1) / M := by field_simp
  rw [this, Real.log_div h1.ne' h0.ne', one_div, Real.log_inv]
  ring


noncomputable def binC (m k : ℕ) : ℝ := m * (H (k / m) - H ((k + 1) / m))

lemma binC_int (m k : ℕ) (hm : 0 < m) (hk : k + 1 ≤ m) :
    ∫ x in (k / m : ℝ)..((k + 1) / m), logit x = binC m k * ((k + 1) / m - k / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
  rw [logit_ftc _ _ (by positivity) (by gcongr; linarith) (by rw [div_le_one hm']; exact hk')]
  unfold binC
  have : ((k : ℝ) + 1) / m - k / m = 1 / m := by field_simp; ring
  rw [this]; field_simp

lemma H_eps (M : ℝ) : H (1 / M) = -(1 / M) * Real.log (1 / M) + -(1 - 1 / M) * Real.log (1 - 1 / M) := by
  unfold H
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]

lemma const_le_of_int (f : ℝ → ℝ) (l r c K : ℝ) (hlr : l < r) (hf : IntervalIntegrable f volume l r)
    (hK : ∀ x ∈ Set.Ioo l r, f x ≤ K) (hint : ∫ x in l..r, f x = c * (r - l)) : c ≤ K := by
  have := int_mono f (fun _ => K) l r hlr.le hf intervalIntegrable_const hK
  simp at this
  have h2 : 0 < r - l := by linarith
  nlinarith

lemma le_const_of_int (f : ℝ → ℝ) (l r c K : ℝ) (hlr : l < r) (hf : IntervalIntegrable f volume l r)
    (hK : ∀ x ∈ Set.Ioo l r, K ≤ f x) (hint : ∫ x in l..r, f x = c * (r - l)) : K ≤ c := by
  have := int_mono (fun _ => K) f l r hlr.le intervalIntegrable_const hf hK
  simp at this
  have h2 : 0 < r - l := by linarith
  nlinarith

lemma left_bound (m : ℕ) (hm : 16 ≤ m) :
    ∫ x in (0 : ℝ)..(1 / m), |logit x - binC m 0| ≤ -2 * Real.log (1 - 1 / m) := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have hε : 0 < 1 / (m : ℝ) := by positivity
  have hε1 : 1 / (m : ℝ) < 1 := by rw [div_lt_one hM0]; linarith
  have hint := binC_int m 0 (by omega) (by omega)
  simp only [Nat.cast_zero, zero_add, zero_div] at hint
  have hb : binC m 0 = - m * H (1 / m) := by unfold binC; simp [H]
  have hK : ∀ x ∈ Set.Ioo (0 : ℝ) (1 / m), logit x ≤ logit (1 / m) :=
    fun x hx => logit_mono hx.1 hx.2.le hε1
  have hcK := const_le_of_int logit 0 (1 / m) _ _ hε (logit_ii _ _) hK hint
  have h := L_left logit 0 (1 / m) _ _ hε.le (logit_ii _ _) hK hcK hint
  refine h.trans (le_of_eq ?_)
  have e : (m : ℝ) * (1 / m) = 1 := by field_simp
  rw [hb, logit_eq, H_eps]
  linear_combination (-(1 / (m:ℝ) * Real.log (1 / m) + (1 - 1 / (m:ℝ)) * Real.log (1 - 1 / m))) * e * 2

lemma right_bound (m : ℕ) (hm : 16 ≤ m) :
    ∫ x in (((m - 1 : ℕ) : ℝ) / m)..(((m - 1 : ℕ) + 1 : ℝ) / m),
      |logit x - binC m (m - 1)| ≤ -2 * Real.log (1 - 1 / m) := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have hε : 0 < 1 / (m : ℝ) := by positivity
  have hε1 : 1 / (m : ℝ) < 1 := by rw [div_lt_one hM0]; linarith
  have hint := binC_int m (m - 1) (by omega) (by omega)
  have hk : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    rw [Nat.cast_sub (by omega)]; simp
  have hl : ((m - 1 : ℕ) : ℝ) / m = 1 - 1 / m := by
    rw [Nat.cast_sub (by omega)]; field_simp; simp
  have hr : (((m - 1 : ℕ) : ℝ) + 1) / m = 1 := by rw [hk]; field_simp
  rw [hr, hl] at hint
  rw [hr, hl]
  have hb : binC m (m - 1) = m * H (1 / m) := by
    unfold binC
    rw [hr, hl]; simp [H]
  have hK : ∀ x ∈ Set.Ioo (1 - 1 / (m : ℝ)) 1, logit (1 - 1 / m) ≤ logit x :=
    fun x hx => logit_mono (by linarith) hx.1.le hx.2
  have hlt : (1 - 1 / (m : ℝ)) < 1 := by linarith
  have hcK := le_const_of_int logit (1 - 1 / m) 1 _ _ hlt (logit_ii _ _) hK hint
  have h := L_right logit (1 - 1 / m) 1 _ _ hlt.le (logit_ii _ _) hK hcK hint
  refine h.trans (le_of_eq ?_)
  have e : (m : ℝ) * (1 / m) = 1 := by field_simp
  rw [hb, logit_eq, H_eps]
  have e2 : (1 - (1 - 1 / (m : ℝ))) = 1 / m := by ring
  rw [e2]
  linear_combination (-(1 / (m:ℝ) * Real.log (1 / m) + (1 - 1 / (m:ℝ)) * Real.log (1 - 1 / m))) * e * 2

lemma mid_bound (m k : ℕ) (hm : 16 ≤ m) (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ m) :
    ∫ x in (k / m : ℝ)..((k + 1) / m), |logit x - binC m k| ≤
      (1 / m) * (logit ((k + 1) / m) - logit (k / m)) := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) + 2 ≤ m := by exact_mod_cast hk2
  have hint := binC_int m k (by omega) (by omega)
  have hlr : (k / m : ℝ) < (k + 1) / m := by gcongr; linarith
  have hl0 : 0 < (k / m : ℝ) := by positivity
  have hr1 : ((k + 1) / m : ℝ) < 1 := by rw [div_lt_one hM0]; linarith
  have hK : ∀ x ∈ Set.Ioo (k / m : ℝ) ((k + 1) / m), logit x ≤ logit ((k + 1) / m) :=
    fun x hx => logit_mono (hl0.trans hx.1) hx.2.le hr1
  have hK' : ∀ x ∈ Set.Ioo (k / m : ℝ) ((k + 1) / m), logit (k / m) ≤ logit x :=
    fun x hx => logit_mono hl0 hx.1.le (hx.2.trans hr1)
  have c1 := const_le_of_int logit _ _ _ _ hlr (logit_ii _ _) hK hint
  have c2 := le_const_of_int logit _ _ _ _ hlr (logit_ii _ _) hK' hint
  have h := L_mid logit _ _ _ _ _ hlr.le (logit_ii _ _) hK hK' c1 c2
  have e : ((k : ℝ) + 1) / m - k / m = 1 / m := by field_simp; ring
  rwa [e] at h


lemma binC_zero (m : ℕ) : binC m 0 = - m * H (1 / m) := by unfold binC; simp [H]

lemma binC_last (m : ℕ) (hm : 1 ≤ m) : binC m (m - 1) = m * H (1 / m) := by
  have hM0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    rw [Nat.cast_sub hm]; simp
  have hl : ((m - 1 : ℕ) : ℝ) / m = 1 - 1 / m := by
    rw [Nat.cast_sub hm]; field_simp; simp
  have hr : (((m - 1 : ℕ) : ℝ) + 1) / m = 1 := by rw [hk]; field_simp
  unfold binC
  rw [hr, hl]; simp [H]

lemma mid_c (m k : ℕ) (hm : 16 ≤ m) (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ m) :
    logit (k / m) ≤ binC m k ∧ binC m k ≤ logit ((k + 1) / m) := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk2' : (k : ℝ) + 2 ≤ m := by exact_mod_cast hk2
  have hint := binC_int m k (by omega) (by omega)
  have hlr : (k / m : ℝ) < (k + 1) / m := by gcongr; linarith
  have hl0 : 0 < (k / m : ℝ) := by positivity
  have hr1 : ((k + 1) / m : ℝ) < 1 := by rw [div_lt_one hM0]; linarith
  have hK : ∀ x ∈ Set.Ioo (k / m : ℝ) ((k + 1) / m), logit x ≤ logit ((k + 1) / m) :=
    fun x hx => logit_mono (hl0.trans hx.1) hx.2.le hr1
  have hK' : ∀ x ∈ Set.Ioo (k / m : ℝ) ((k + 1) / m), logit (k / m) ≤ logit x :=
    fun x hx => logit_mono hl0 hx.1.le (hx.2.trans hr1)
  exact ⟨le_const_of_int logit _ _ _ _ hlr (logit_ii _ _) hK' hint,
    const_le_of_int logit _ _ _ _ hlr (logit_ii _ _) hK hint⟩

lemma neglog_le (m : ℕ) (hm : 16 ≤ m) : -Real.log (1 - 1 / m) ≤ 1 / (m - 1) := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℝ) < 1 - 1 / m := by
    have : 1 / (m : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at this
  have e : (1 - 1 / (m : ℝ))⁻¹ - 1 = 1 / (m - 1) := by
    have : (m : ℝ) - 1 ≠ 0 := by linarith
    have : (m : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  linarith

lemma end_bound (m : ℕ) (hm : 16 ≤ m) : (m : ℝ) * H (1 / m) ≤ Real.log m + 1 := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have e : (m : ℝ) * (1 / m) = 1 := by field_simp
  have h : (m : ℝ) * H (1 / m) = -Real.log (1 / m) + (m - 1) * (-Real.log (1 - 1 / m)) := by
    rw [H_eps]
    linear_combination (Real.log (1 - 1 / m) - Real.log (1 / m)) * e
  have := neglog_le m hm
  have h2 : ((m : ℝ) - 1) * (-Real.log (1 - 1 / m)) ≤ 1 := by
    calc ((m : ℝ) - 1) * (-Real.log (1 - 1 / m)) ≤ ((m : ℝ) - 1) * (1 / (m - 1)) :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = 1 := by
          have : (m : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  have hl : Real.log (1 / (m : ℝ)) = -Real.log m := by rw [one_div, Real.log_inv]
  rw [h, hl]
  linarith

lemma part1 (m : ℕ) (hm : 16 ≤ m) (j : Fin m) : |binScore m j| ≤ Real.log m + 1 := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have hH : 0 ≤ H (1 / (m : ℝ)) := by
    unfold H
    apply Real.binEntropy_nonneg
    · positivity
    · rw [div_le_one hM0]; linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  obtain ⟨k, hk⟩ := j
  show |binC m k| ≤ _
  by_cases h0 : k = 0
  · subst h0
    simp only [binC_zero]
    have := end_bound m hm
    rw [abs_le]; constructor <;> nlinarith
  by_cases h1 : k = m - 1
  · subst h1
    simp only [binC_last m (by omega)]
    have := end_bound m hm
    rw [abs_le]; constructor <;> nlinarith
  · obtain ⟨c1, c2⟩ := mid_c m k hm (by omega) (by omega)
    have hl0 : (1 / (m : ℝ)) ≤ k / m := by
      gcongr; exact_mod_cast (by omega : 1 ≤ k)
    have hr1 : ((k + 1) / m : ℝ) ≤ 1 - 1 / m := by
      rw [← sub_nonneg]
      have : (1 : ℝ) - 1 / m - (k + 1) / m = ((m : ℝ) - 2 - k) / m := by field_simp; ring
      rw [this]
      apply div_nonneg _ hM0.le
      have : (k : ℝ) + 2 ≤ m := by exact_mod_cast (by omega : k + 2 ≤ m)
      linarith
    have hkm : (k : ℝ) / m < 1 := by
      rw [div_lt_one hM0]; exact_mod_cast hk
    have a1 := logit_mono (by positivity : (0 : ℝ) < 1 / m) hl0 hkm
    have a2 := logit_mono (by positivity : (0 : ℝ) < (k + 1) / m) hr1
      (by have : 0 < 1 / (m : ℝ) := by positivity
          linarith)
    rw [logit_one_sub, logit_inv _ (by linarith)] at a2
    rw [logit_inv _ (by linarith)] at a1
    have hl : Real.log ((m : ℝ) - 1) ≤ Real.log m := Real.log_le_log (by linarith) (by linarith)
    rw [abs_le]; constructor <;> linarith
  

lemma binScoreAt_eq (m k : ℕ) (hk : k < m) (u : ℝ) (hu : u ∈ Set.Ioo ((k : ℝ) / m) (((k : ℝ) + 1) / m)) :
    binScoreAt m u = binC m k := by
  have hM0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 : (k : ℝ) < m * u := by
    have := hu.1; rw [div_lt_iff₀ hM0] at this; linarith
  have h2 : (m : ℝ) * u < k + 1 := by
    have := hu.2; rw [lt_div_iff₀ hM0] at this; linarith
  have hf : ⌊(m : ℝ) * u⌋ = (k : ℤ) := Int.floor_eq_iff.2 ⟨by exact_mod_cast h1.le, by push_cast; linarith⟩
  have hb : binOf m u = k := by unfold binOf; rw [hf]; simp
  unfold binScoreAt
  rw [dif_pos (by rw [hb]; exact hk)]
  simp only [hb]
  rfl

lemma bin_int_eq (m k : ℕ) (hk : k < m) :
    IntervalIntegrable (fun u => |logit u - binScoreAt m u|) volume (k / m : ℝ) ((k + 1) / m) ∧
    ∫ u in (k / m : ℝ)..((k + 1) / m), |logit u - binScoreAt m u| =
      ∫ u in (k / m : ℝ)..((k + 1) / m), |logit u - binC m k| := by
  have hM0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlr : (k / m : ℝ) ≤ (k + 1) / m := by gcongr; linarith
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (k / m : ℝ) ((k + 1) / m) →
      |logit u - binScoreAt m u| = |logit u - binC m k| := by
    have : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ ((k : ℝ) + 1) / m := by
      simp [ae_iff]
    filter_upwards [this] with u hu hmem
    rw [Set.uIoc_of_le hlr] at hmem
    rw [binScoreAt_eq m k hk u ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩]
  refine ⟨?_, intervalIntegral.integral_congr_ae hae⟩
  have h2 : IntervalIntegrable (fun u => |logit u - binC m k|) volume (k / m : ℝ) ((k + 1) / m) :=
    ((logit_ii _ _).sub intervalIntegrable_const).abs
  rw [intervalIntegrable_iff] at h2 ⊢
  refine h2.congr_fun_ae ?_
  have := (ae_restrict_iff' (μ := volume) measurableSet_uIoc).2 hae
  filter_upwards [this] with u hu using hu.symm


noncomputable def Bk (m k : ℕ) : ℝ :=
  ∫ x in (k / m : ℝ)..(((k : ℝ) + 1) / m), |logit x - binC m k|

lemma end_small (m : ℕ) (hm : 16 ≤ m) : -2 * Real.log (1 - 1 / m) ≤ 3 / m := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have h := neglog_le m hm
  have h2 : 1 / ((m : ℝ) - 1) ≤ 3 / 2 * (1 / m) := by
    rw [div_le_iff₀ (by linarith)]
    have : 3 / 2 * (1 / (m : ℝ)) * (m - 1) = 3 / 2 - 3 / 2 * (1 / m) := by field_simp
    rw [this]
    have : 1 / (m : ℝ) ≤ 1 / 16 := by gcongr
    linarith
  have : 3 / (m : ℝ) = 3 * (1 / m) := by ring
  rw [this]; linarith

lemma sum_bound (m : ℕ) (hm : 16 ≤ m) :
    ∑ k ∈ Finset.range m, Bk m k ≤ (2 * Real.log m + 6) / m := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  obtain ⟨n, hn⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have key : ∀ g : ℕ → ℝ, ∑ k ∈ Finset.range m, g k =
      g 0 + ∑ i ∈ Finset.range n, g (i + 1) + g (n + 1) := by
    intro g
    rw [show m = n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ']
    ring
  rw [key]
  have hmr : (m : ℝ) = n + 2 := by exact_mod_cast hn
  have b0 : Bk m 0 ≤ 3 / m := by
    have e1 : ((0 : ℕ) : ℝ) / m = 0 := by simp
    have e2 : (((0 : ℕ) : ℝ) + 1) / m = 1 / m := by simp
    unfold Bk; rw [e1, e2]
    exact (left_bound m hm).trans (end_small m hm)
  have b1 : Bk m (n + 1) ≤ 3 / m := by
    have : n + 1 = m - 1 := by omega
    unfold Bk; rw [this]
    exact (right_bound m hm).trans (end_small m hm)
  set f : ℕ → ℝ := fun i => logit (((i : ℝ) + 1) / m) with hf
  have bm : ∑ i ∈ Finset.range n, Bk m (i + 1) ≤ ∑ i ∈ Finset.range n, (1 / (m : ℝ)) * (f (i + 1) - f i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have := mid_bound m (i + 1) hm (by omega) (by omega)
    unfold Bk
    simp only [hf]
    have e : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [e] at this ⊢
    exact this
  rw [← Finset.mul_sum, Finset.sum_range_sub] at bm
  have hfn : f n = Real.log ((m : ℝ) - 1) := by
    have : ((n : ℝ) + 1) / m = 1 - 1 / m := by rw [hmr]; field_simp; ring
    simp only [hf]; rw [this, logit_one_sub, logit_inv _ (by linarith)]; ring
  have hf0 : f 0 = - Real.log ((m : ℝ) - 1) := by
    simp only [hf]; have := logit_inv (m : ℝ) (by linarith); simpa using this
  have hl : Real.log ((m : ℝ) - 1) ≤ Real.log m := Real.log_le_log (by linarith) (by linarith)
  rw [hfn, hf0] at bm
  have : (2 * Real.log m + 6) / (m : ℝ) = (1 / m) * (2 * Real.log m) + 3 / m + 3 / m := by
    field_simp; ring
  rw [this]
  have : (1 / (m : ℝ)) * (Real.log ((m : ℝ) - 1) - -Real.log ((m : ℝ) - 1)) ≤ (1 / m) * (2 * Real.log m) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  linarith

lemma part2 (m : ℕ) (hm : 16 ≤ m) :
    (∫ u in Set.Ioo (0 : ℝ) 1, |logit u - binScoreAt m u|) ≤ (2 * Real.log m + 6) / m := by
  have hM : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by linarith
  have hI : ∫ u in Set.Ioo (0 : ℝ) 1, |logit u - binScoreAt m u| =
      ∫ u in (0 : ℝ)..1, |logit u - binScoreAt m u| := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hc : ∀ k : ℕ, (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := fun k => by push_cast; ring
  have hint : ∀ k < m, IntervalIntegrable (fun u => |logit u - binScoreAt m u|) volume
      ((fun k : ℕ => (k : ℝ) / m) k) ((fun k : ℕ => (k : ℝ) / m) (k + 1)) := by
    intro k hk
    show IntervalIntegrable _ volume ((k : ℝ) / m) (((k + 1 : ℕ) : ℝ) / m)
    rw [hc]; exact (bin_int_eq m k hk).1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) hint
  have e0 : ((0 : ℕ) : ℝ) / m = 0 := by simp
  have em : ((m : ℕ) : ℝ) / m = 1 := by field_simp
  simp only [e0, em] at hsum
  rw [hI, ← hsum]
  refine le_trans (le_of_eq ?_) (sum_bound m hm)
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.1 hk
  show ∫ u in (k / m : ℝ)..(((k + 1 : ℕ) : ℝ) / m), |logit u - binScoreAt m u| = Bk m k
  rw [hc]
  exact (bin_int_eq m k hk').2

lemma m_ge (d : ℕ) (hd : 2 ≤ d) : 16 ≤ numBins d := by
  have h : 64 * d ≤ 2 ^ paramS d := Nat.find_spec (⟨64 * d, (Nat.lt_two_pow_self).le⟩ : ∃ j, 64 * d ≤ 2 ^ j)
  unfold numBins
  have h2 : 2 ^ paramS d ≤ 4 ^ paramS d := Nat.pow_le_pow_left (by norm_num) _
  omega

end LogSupermodularBIS.Main

open LogSupermodularBIS.Main in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ j : Fin (numBins d), |binScore (numBins d) j| ≤ paramA0 d) ∧
    (∫ u in Set.Ioo (0 : ℝ) 1, |logit u - binScoreAt (numBins d) u|) ≤
      (2 * Real.log (numBins d) + 6) / (numBins d) :=
  ⟨part1 _ (m_ge d hd), part2 _ (m_ge d hd)⟩
