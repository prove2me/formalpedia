-- Prove2me | solution 1 for LuoSunLiu.DIP.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:37:54.875224+00:00
-- url     : https://prove2.me/submissions/9b98466d-1551-49de-8b06-a912eaa8060b

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_Policy
import Theorems.Thm_LuoSunLiu_DIP_proposition_3_conditional

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP.Thm1Aux
open LuoSunLiu.DIP

theorem epEnd_succ (α1 α2 k : ℕ) (hk : 1 ≤ k) :
    epEnd α1 α2 (k + 1) = epEnd α1 α2 k + 2 ^ (k - 1) * α2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [epEnd, Nat.add_sub_cancel]
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ m = q + 1 := ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
  rw [pow_succ, hq]
  have : (q + 1) * 2 - 1 = 2 * q + 1 := by omega
  rw [this, Nat.add_sub_cancel]
  ring

theorem epEnd_zero (α1 α2 : ℕ) : epEnd α1 α2 0 = α1 := by simp [epEnd]
theorem epEnd_one (α1 α2 : ℕ) : epEnd α1 α2 1 = α1 := by simp [epEnd]

theorem epEnd_mono (α1 α2 : ℕ) : Monotone (epEnd α1 α2) := by
  apply monotone_nat_of_le_succ
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [epEnd_zero, epEnd_one]
  · rw [epEnd_succ α1 α2 k hk]; omega

theorem le_epEnd (α1 α2 : ℕ) (hα2 : 1 ≤ α2) (T : ℕ) : T ≤ epEnd α1 α2 (T + 1) := by
  simp only [epEnd, Nat.add_sub_cancel]
  have h1 : T < 2 ^ T := Nat.lt_two_pow_self
  have h2 : 2 ^ T - 1 ≤ α2 * (2 ^ T - 1) := Nat.le_mul_of_pos_left _ hα2
  omega

theorem epEnd_eq (α1 α2 k : ℕ) (hk : 2 ≤ k) :
    epEnd α1 α2 k = epEnd α1 α2 (k - 1) + 2 ^ (k - 2) * α2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [epEnd_succ α1 α2 m (by omega)]
  simp only [Nat.add_sub_cancel]
  congr 2

theorem nEp_spec (α1 α2 T : ℕ) (hα2 : 1 ≤ α2) :
    1 ≤ nEp α1 α2 T ∧ T ≤ epEnd α1 α2 (nEp α1 α2 T) ∧
      (2 ≤ nEp α1 α2 T → epEnd α1 α2 (nEp α1 α2 T - 1) < T) := by
  have hne : {k : ℕ | 1 ≤ k ∧ T ≤ epEnd α1 α2 k}.Nonempty :=
    ⟨T + 1, by omega, le_epEnd α1 α2 hα2 T⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun h2 => ?_⟩
  have hlt : nEp α1 α2 T - 1 < nEp α1 α2 T := by omega
  have := Nat.notMem_of_lt_sInf hlt
  simp only [Set.mem_ofPred_eq, not_and, not_le] at this
  exact this (by omega)

theorem sum_decomp (α1 α2 : ℕ) (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Finset.Ioc 0 (epEnd α1 α2 n), f t =
      ∑ t ∈ Finset.Ioc 0 α1, f t +
        ∑ k ∈ Finset.Icc 2 n, ∑ t ∈ Finset.Ioc (epEnd α1 α2 (k - 1)) (epEnd α1 α2 k), f t := by
  induction n, hn using Nat.le_induction with
  | base => simp [epEnd_one]
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih, Nat.add_sub_cancel]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (epEnd_mono α1 α2 (Nat.le_succ m))]


theorem price_mem {d0 : ℕ} (M : PricingModel d0) (α1 α2 Cdisc : ℕ) (lam : ℝ)
    (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ))
    {Ω : Type*} (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (ω : Ω)
    (hrun : IsDIPRun M α1 α2 Cdisc lam est x z p ω) (hα2 : 1 ≤ α2) (t : ℕ) (ht : 1 ≤ t) :
    p t ω ∈ Set.Ioo 0 M.pmax := by
  by_cases h1 : t ≤ α1
  · exact hrun.1 t (Finset.mem_Icc.2 ⟨ht, h1⟩)
  have hex : ∃ k, t ≤ epEnd α1 α2 k := ⟨t + 1, le_epEnd α1 α2 hα2 t⟩
  set k := Nat.find hex with hkdef
  have hk : t ≤ epEnd α1 α2 k := Nat.find_spec hex
  have hk2 : 2 ≤ k := by
    by_contra hc
    interval_cases hk' : k
    · simp [epEnd_zero] at hk; omega
    · simp [epEnd_one] at hk; omega
  have hkmin : ¬ t ≤ epEnd α1 α2 (k - 1) := Nat.find_min hex (by omega)
  have hE := epEnd_eq α1 α2 k hk2
  obtain ⟨j, hj⟩ := hrun.2 k hk2
  have hlen : epLen α1 α2 k = 2 ^ (k - 2) * α2 := by simp [epLen]; omega
  have hτ : t - epEnd α1 α2 (k - 1) ∈ Finset.Icc 1 (epLen α1 α2 k) := by
    rw [hlen, Finset.mem_Icc]; omega
  obtain ⟨hav, hpr, -, -⟩ := hj _ hτ
  have heq : epEnd α1 α2 (k - 1) + (t - epEnd α1 α2 (k - 1)) = t := by omega
  rw [heq] at hav hpr
  simp only at hpr
  rw [hpr]
  simp only [avail, Finset.mem_filter] at hav
  exact ⟨hav.2.1, hav.2.2⟩

theorem F_bounds {d0 : ℕ} (M : PricingModel d0) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p) (c : ℝ) :
    0 ≤ M.F c ∧ M.F c ≤ 1 := by
  obtain ⟨-, -, -, -, hF, -⟩ := hEnv 1 le_rfl
  rw [← hF c]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem perRegret_bounds {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing)
    (hF : ∀ c, 0 ≤ M.F c ∧ M.F c ≤ 1) (y : Fin d0 → ℝ) (hy : y ∈ M.X) (q : ℝ)
    (hq : q ∈ Set.Ioo 0 M.pmax) : 0 ≤ perRegret M y q ∧ perRegret M y q ≤ M.pmax := by
  obtain ⟨-, -, -, hst⟩ := hM
  obtain ⟨⟨hs0, hs1⟩, hmax⟩ := hst y hy
  unfold perRegret
  refine ⟨by linarith [hmax q hq.1], ?_⟩
  unfold revenue
  have h1 := hF (M.pstar y - y ⬝ᵥ M.θ0)
  have h2 := hF (q - y ⬝ᵥ M.θ0)
  have : 0 ≤ q * (1 - M.F (q - y ⬝ᵥ M.θ0)) := mul_nonneg hq.1.le (by linarith)
  nlinarith

theorem revenue_eq_iSup (F : ℝ → ℝ) (hF : Continuous F) (q a : ℝ) (ha : 0 < a)
    (hmax : ∀ r : ℝ, 0 < r → revenue F q r ≤ revenue F q a) :
    revenue F q a = ⨆ r : {r : ℚ // (0 : ℝ) < r}, revenue F q (r.1 : ℝ) := by
  have hbdd : BddAbove (Set.range fun r : {r : ℚ // (0 : ℝ) < r} => revenue F q (r.1 : ℝ)) :=
    ⟨revenue F q a, by rintro _ ⟨r, rfl⟩; exact hmax _ r.2⟩
  have : Nonempty {r : ℚ // (0 : ℝ) < r} := ⟨⟨1, by norm_num⟩⟩
  apply le_antisymm
  · have hc : Continuous (fun r => revenue F q r) := by
      unfold revenue; fun_prop
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hc a ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max (a - δ) (a / 2) < a by
      rcases max_cases (a - δ) (a / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_right _ _) hr1)
    have hd : dist (r : ℝ) a < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_left (a - δ) (a / 2)]
    have := hball r hd
    rw [Real.dist_eq, abs_lt] at this
    have hle : revenue F q (r : ℝ) ≤ ⨆ r : {r : ℚ // (0 : ℝ) < r}, revenue F q (r.1 : ℝ) :=
      le_ciSup hbdd ⟨r, hr0⟩
    linarith [this.1]
  · exact ciSup_le fun r => hmax _ r.2

theorem perRegret_measurable {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) {Ω : Type*} [MeasurableSpace Ω] (x : Ω → Fin d0 → ℝ)
    (q : Ω → ℝ) (hx : Measurable x) (hq : Measurable q) (hX : ∀ ω, x ω ∈ M.X) :
    Measurable fun ω => perRegret M (x ω) (q ω) := by
  have hFc : Continuous M.F := hL.continuous
  have hrev : Continuous (fun v : ℝ × ℝ => revenue M.F v.1 v.2) := by
    unfold revenue; fun_prop
  have heq : (fun ω => perRegret M (x ω) (q ω)) = fun ω =>
      (⨆ r : {r : ℚ // (0 : ℝ) < r}, revenue M.F (x ω ⬝ᵥ M.θ0) (r.1 : ℝ)) -
        revenue M.F (x ω ⬝ᵥ M.θ0) (q ω) := by
    funext ω
    obtain ⟨-, -, -, hst⟩ := hM
    obtain ⟨⟨hs0, -⟩, hmax⟩ := hst (x ω) (hX ω)
    unfold perRegret
    rw [revenue_eq_iSup M.F hFc _ _ hs0 hmax]
  rw [heq]
  have hdot : Measurable fun ω => x ω ⬝ᵥ M.θ0 := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hx).mul_const _
  refine Measurable.sub ?_ ?_
  · refine Measurable.iSup fun r => ?_
    exact hrev.measurable.comp (hdot.prodMk measurable_const)
  · exact hrev.measurable.comp (hdot.prodMk hq)


theorem geom_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 n, b ^ (n - k) ≤ 1 / (1 - b) := by
  have hpos : 0 < 1 - b := by linarith
  rcases Nat.lt_or_ge n 1 with hn | hn
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; exact (one_div_pos.2 hpos).le
  induction n, hn using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; exact (one_div_pos.2 hpos).le
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero]
    have : ∑ k ∈ Finset.Icc 2 m, b ^ (m + 1 - k) = b * ∑ k ∈ Finset.Icc 2 m, b ^ (m - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]; ring
    rw [this]
    have h2 : b * ∑ k ∈ Finset.Icc 2 m, b ^ (m - k) ≤ b * (1 / (1 - b)) :=
      mul_le_mul_of_nonneg_left ih hb0
    have h3 : b * (1 / (1 - b)) + 1 = 1 / (1 - b) := by field_simp; ring
    linarith

theorem rpow_split (α2 k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) =
      (((2 ^ (n - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) * ((2 : ℝ) ^ (-((2 : ℝ) / 3))) ^ (n - k) := by
  have hnat : 2 ^ (n - 2) * α2 = 2 ^ (n - k) * (2 ^ (k - 2) * α2) := by
    rw [← mul_assoc, ← pow_add]; congr 2; omega
  set A : ℝ := (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) with hA
  have hcast : (((2 ^ (n - k) * (2 ^ (k - 2) * α2) : ℕ) : ℝ)) = (2 : ℝ) ^ (n - k) * A := by
    rw [hA]; push_cast; ring
  rw [hnat, hcast, Real.mul_rpow (by positivity) (by positivity)]
  have h1 : ((2 : ℝ) ^ (n - k)) ^ ((2 : ℝ) / 3) * ((2 : ℝ) ^ (-((2 : ℝ) / 3))) ^ (n - k) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    ring_nf; simp
  calc A ^ ((2 : ℝ) / 3)
      = A ^ ((2 : ℝ) / 3) *
          (((2 : ℝ) ^ (n - k)) ^ ((2 : ℝ) / 3) * ((2 : ℝ) ^ (-((2 : ℝ) / 3))) ^ (n - k)) := by
        rw [h1, mul_one]
    _ = _ := by ring


/-- The constant of Theorem 1 built from the episode constants. -/
noncomputable def Cc (α1 α2 : ℕ) (pmax C2 C3 : ℝ) : ℝ :=
  α1 * pmax / Real.log 2 + C3 * (|Real.log (C2 * (1 + α2))| / Real.log 2 + 1) *
    ((1 : ℝ) + α2) ^ ((2 : ℝ) / 3) / (1 - (2 : ℝ) ^ (-((2 : ℝ) / 3)))

theorem b_lt_one : (2 : ℝ) ^ (-((2 : ℝ) / 3)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem Cc_pos (α1 α2 : ℕ) (pmax C2 C3 : ℝ) (hp : 0 < pmax) (hC3 : 0 < C3) :
    0 < Cc α1 α2 pmax C2 C3 := by
  unfold Cc
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < 1 - (2 : ℝ) ^ (-((2 : ℝ) / 3)) := by linarith [b_lt_one]
  have h1 : 0 ≤ α1 * pmax / Real.log 2 := by positivity
  have h2 : 0 < C3 * (|Real.log (C2 * (1 + α2))| / Real.log 2 + 1) *
      ((1 : ℝ) + α2) ^ ((2 : ℝ) / 3) / (1 - (2 : ℝ) ^ (-((2 : ℝ) / 3))) := by positivity
  linarith

theorem final_real (α1 α2 : ℕ) (hα2 : 1 ≤ α2) (pmax C2 C3 : ℝ) (hp : 0 < pmax) (hC2 : 0 < C2)
    (hC3 : 0 < C3) (T n : ℕ) (hT : 2 ≤ T) (hn : 2 ≤ n → 2 ^ (n - 2) * α2 < T + α2) :
    α1 * pmax + ∑ k ∈ Finset.Icc 2 n, max 0 (C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
        (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3)) ≤
      Cc α1 α2 pmax C2 C3 * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log T := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hLg : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT'
  set Lg := Real.log (T : ℝ) with hLgdef
  set Pw := (T : ℝ) ^ ((2 : ℝ) / 3) with hPw
  have hP1 : 1 ≤ Pw := Real.one_le_rpow (by linarith) (by norm_num)
  set b := (2 : ℝ) ^ (-((2 : ℝ) / 3)) with hb
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := b_lt_one
  have hb1' : 0 < 1 - b := by linarith
  set K := |Real.log (C2 * (1 + α2))| / Real.log 2 + 1 with hK
  have hK0 : 0 < K := by positivity
  have hα2' : (1 : ℝ) ≤ α2 := by exact_mod_cast hα2
  -- part 1
  have hpart1 : (α1 : ℝ) * pmax ≤ α1 * pmax / Real.log 2 * Pw * Lg := by
    have h0 : 0 ≤ (α1 : ℝ) * pmax / Real.log 2 := by positivity
    have : Real.log 2 ≤ Pw * Lg := by nlinarith
    calc (α1 : ℝ) * pmax = α1 * pmax / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ α1 * pmax / Real.log 2 * (Pw * Lg) := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  -- part 2
  have hpart2 : ∑ k ∈ Finset.Icc 2 n, max 0 (C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
        (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3)) ≤
      C3 * K * ((1 : ℝ) + α2) ^ ((2 : ℝ) / 3) / (1 - b) * Pw * Lg := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
    have hln : (((2 ^ (n - 2) * α2 : ℕ) : ℝ)) ≤ (1 + α2) * T := by
      have h := hn hn2
      have h' : (((2 ^ (n - 2) * α2 : ℕ) : ℝ)) < T + α2 := by exact_mod_cast h
      nlinarith
    have hterm : ∀ k ∈ Finset.Icc 2 n,
        max 0 (C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
          (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3)) ≤
        C3 * K * Lg * (((1 + α2) * T) ^ ((2 : ℝ) / 3)) * b ^ (n - k) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hlk_pos : (0 : ℝ) < ((2 ^ (k - 2) * α2 : ℕ) : ℝ) := by
        have : 0 < 2 ^ (k - 2) * α2 := by positivity
        exact_mod_cast this
      have hlk : (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ≤ (1 + α2) * T := by
        refine le_trans ?_ hln
        have : 2 ^ (k - 2) * α2 ≤ 2 ^ (n - 2) * α2 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        exact_mod_cast this
      have hlog : Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ≤ K * Lg := by
        have h1 : Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ≤ Real.log (C2 * (1 + α2) * T) :=
          Real.log_le_log (by positivity) (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlk hC2.le)
        have h2 : Real.log (C2 * (1 + α2) * T) = Real.log (C2 * (1 + α2)) + Lg :=
          Real.log_mul (by positivity) (by positivity)
        have h3 : Real.log (C2 * (1 + α2)) ≤ |Real.log (C2 * (1 + α2))| / Real.log 2 * Lg := by
          have h4 : |Real.log (C2 * (1 + α2))| ≤ |Real.log (C2 * (1 + α2))| / Real.log 2 * Lg := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
            exact mul_le_mul_of_nonneg_left hLg (abs_nonneg _)
          exact le_trans (le_abs_self _) h4
        rw [hK]; nlinarith
      have hsplit := rpow_split α2 k n hk.1 hk.2
      have hrp : (((2 ^ (n - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) ≤ ((1 + α2) * T) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) hln (by norm_num)
      have hbk : 0 ≤ b ^ (n - k) := pow_nonneg hb0 _
      have hlk23 : (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) ≤
          ((1 + α2) * T) ^ ((2 : ℝ) / 3) * b ^ (n - k) := by
        rw [hsplit]; exact mul_le_mul_of_nonneg_right hrp hbk
      have hnn : 0 ≤ (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) := by positivity
      have hKL : 0 ≤ K * Lg := by positivity
      apply max_le
      · positivity
      calc C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
            (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3)
          ≤ C3 * (K * Lg) * (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC3.le) hnn
        _ ≤ C3 * (K * Lg) * (((1 + α2) * T) ^ ((2 : ℝ) / 3) * b ^ (n - k)) :=
            mul_le_mul_of_nonneg_left hlk23 (by positivity)
        _ = _ := by ring
    calc _ ≤ ∑ k ∈ Finset.Icc 2 n, C3 * K * Lg * (((1 + α2) * T) ^ ((2 : ℝ) / 3)) * b ^ (n - k) :=
          Finset.sum_le_sum hterm
      _ = C3 * K * Lg * (((1 + α2) * T) ^ ((2 : ℝ) / 3)) * ∑ k ∈ Finset.Icc 2 n, b ^ (n - k) := by
          rw [Finset.mul_sum]
      _ ≤ C3 * K * Lg * (((1 + α2) * T) ^ ((2 : ℝ) / 3)) * (1 / (1 - b)) :=
          mul_le_mul_of_nonneg_left (geom_bound b hb0 hb1 n) (by positivity)
      _ = _ := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← hPw]
          field_simp
  have hCc : Cc α1 α2 pmax C2 C3 * Pw * Lg =
      α1 * pmax / Real.log 2 * Pw * Lg + C3 * K * ((1 : ℝ) + α2) ^ ((2 : ℝ) / 3) / (1 - b) * Pw * Lg := by
    unfold Cc; rw [← hb, ← hK]; ring
  rw [hCc]
  linarith


theorem ep_index (α1 α2 m : ℕ) (hm : 1 ≤ m) (i : ℕ) (hi : i < epLen α1 α2 m) :
    1 ≤ epStart α1 α2 m + i ∧ epStart α1 α2 m + i ≤ epEnd α1 α2 m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this
    simp only [epLen, le_refl, if_true] at hi
    simp only [epStart, le_refl, if_true, epEnd_one]; omega
  · have hs : epStart α1 α2 m = epEnd α1 α2 (m - 1) + 1 := by simp [epStart]; omega
    have hl : epLen α1 α2 m = 2 ^ (m - 2) * α2 := by simp [epLen]; omega
    rw [hl] at hi
    rw [hs, epEnd_eq α1 α2 m h]; omega

theorem resp_meas {d0 : ℕ} (θ0 : Fin d0 → ℝ) {Ω : Type*} [mm : MeasurableSpace Ω]
    (xt : Ω → Fin d0 → ℝ) (zt pt : Ω → ℝ) (hx : Measurable xt) (hz : Measurable zt)
    (hp : Measurable pt) :
    Measurable fun ω => if pt ω ≤ xt ω ⬝ᵥ θ0 + zt ω then (1 : ℝ) else 0 := by
  have hdot : Measurable fun ω => xt ω ⬝ᵥ θ0 := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hx).mul_const _
  exact Measurable.ite (measurableSet_le hp (hdot.add hz)) measurable_const measurable_const

theorem data_meas {d0 : ℕ} {Ω : Type*} [mm : MeasurableSpace Ω] (n : ℕ)
    (f : Fin n → Ω → Fin d0 → ℝ) (g h : Fin n → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i)) :
    Measurable fun ω => fun i => (f i ω, g i ω, h i ω) :=
  measurable_pi_lambda _ fun i => (hf i).prodMk ((hg i).prodMk (hh i))

theorem thetaHat_meas {d0 : ℕ} (M : PricingModel d0) (α1 α2 : ℕ) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝒢 : Filtration ℕ mΩ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (hEnv : IsPricingEnv M P 𝒢 x z p)
    (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ))
    (hest : IsAdmissibleEstimator M α1 α2 est) (m : ℕ) (hm : 1 ≤ m) :
    Measurable[𝒢 (epEnd α1 α2 m)] (thetaHat M α1 α2 est x z p m) := by
  have hcomp : ∀ i : Fin (epLen α1 α2 m),
      Measurable[𝒢 (epEnd α1 α2 m)] (x (epStart α1 α2 m + i)) ∧
      Measurable[𝒢 (epEnd α1 α2 m)] (p (epStart α1 α2 m + i)) ∧
      Measurable[𝒢 (epEnd α1 α2 m)] (response M x z p (epStart α1 α2 m + i)) := by
    intro i
    obtain ⟨h1, h2⟩ := ep_index α1 α2 m hm i i.2
    set t := epStart α1 α2 m + (i : ℕ)
    obtain ⟨hx, hp, hz, -⟩ := hEnv t h1
    have hx' : Measurable[𝒢 (epEnd α1 α2 m)] (x t) := hx.mono (𝒢.mono (by omega)) le_rfl
    have hp' : Measurable[𝒢 (epEnd α1 α2 m)] (p t) := hp.mono (𝒢.mono (by omega)) le_rfl
    have hz' : Measurable[𝒢 (epEnd α1 α2 m)] (z t) := hz.mono (𝒢.mono h2) le_rfl
    exact ⟨hx', hp', resp_meas (Ω := Ω) (mm := 𝒢 (epEnd α1 α2 m)) M.θ0 (x t) (z t) (p t) hx' hz' hp'⟩
  have hdata := data_meas (mm := 𝒢 (epEnd α1 α2 m)) (epLen α1 α2 m)
    (fun i => x (epStart α1 α2 m + i)) (fun i => p (epStart α1 α2 m + i))
    (fun i => response M x z p (epStart α1 α2 m + i))
    (fun i => (hcomp i).1) (fun i => (hcomp i).2.1) (fun i => (hcomp i).2.2)
  exact (hest m).1.comp hdata

end LuoSunLiu.DIP.Thm1Aux

open LuoSunLiu.DIP LuoSunLiu.DIP.Thm1Aux in
theorem solution {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA)
    (α1 α2 Cdisc : ℕ) (hα1 : 1 ≤ α1) (hα2 : 1 ≤ α2)
    (hCdisc : M.pmax + 2 * M.W < Cdisc * M.pmax) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ)
        (est : (k : ℕ) → (Fin (epLen α1 α2 k) → (Fin d0 → ℝ) × ℝ × ℝ) → (Fin d0 → ℝ)),
        IsPricingEnv M P 𝒢 x z p → IsAdmissibleEstimator M α1 α2 est →
        (∀ ω, IsDIPRun M α1 α2 Cdisc lam est x z p ω) →
        ∀ T : ℕ, 2 ≤ T →
          ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T ω) ∂P ≤
            ENNReal.ofReal (C * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log T) +
              ENNReal.ofReal (4 * M.pmax * L) *
                ∑ k ∈ Finset.Icc 2 (nEp α1 α2 T),
                  ((2 ^ (k - 2) * α2 : ℕ) : ℝ≥0∞) *
                    ∫⁻ ω, ENNReal.ofReal
                      (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P := by
  obtain ⟨C2, C3, hC2, hC3, hchild⟩ :=
    proposition_3_conditional M hM L hL CA hA2 Cdisc hCdisc lam hlam
  have hp : 0 < M.pmax := hM.2.1
  refine ⟨Cc α1 α2 M.pmax C2 C3, Cc_pos _ _ _ _ _ hp hC3, ?_⟩
  intro Ω mΩ _ P _ 𝒢 x z p est hEnv hest hrun T hT
  obtain ⟨hn1, hnT, hnprev⟩ := nEp_spec α1 α2 T hα2
  set n := nEp α1 α2 T with hn
  have hFb := F_bounds M P 𝒢 x z p hEnv
  have hX : ∀ t, 1 ≤ t → ∀ ω, x t ω ∈ M.X := fun t ht => (hEnv t ht).2.2.2.1
  have hxm : ∀ t, 1 ≤ t → Measurable (x t) := fun t ht => (hEnv t ht).1.mono (𝒢.le _) le_rfl
  have hpm : ∀ t, 1 ≤ t → Measurable (p t) := fun t ht => (hEnv t ht).2.1.mono (𝒢.le _) le_rfl
  have hr : ∀ t, 1 ≤ t → ∀ ω, 0 ≤ perRegret M (x t ω) (p t ω) ∧
      perRegret M (x t ω) (p t ω) ≤ M.pmax := fun t ht ω =>
    perRegret_bounds M hM hFb _ (hX t ht ω) _ (price_mem M α1 α2 Cdisc lam est x z p ω (hrun ω) hα2 t ht)
  have hrm : ∀ t, 1 ≤ t → Measurable (fun ω => perRegret M (x t ω) (p t ω)) := fun t ht =>
    perRegret_measurable M hM L hL (x t) (p t) (hxm t ht) (hpm t ht) (hX t ht)
  set E : ℕ → Ω → ℝ := fun k ω => ∑ t ∈ Finset.Ioc (epEnd α1 α2 (k - 1)) (epEnd α1 α2 k),
    perRegret M (x t ω) (p t ω) with hE
  set E1 : Ω → ℝ := fun ω => ∑ t ∈ Finset.Ioc 0 α1, perRegret M (x t ω) (p t ω) with hE1
  have hEnn : ∀ k ω, 0 ≤ E k ω := fun k ω => Finset.sum_nonneg fun t ht =>
    (hr t (by rw [Finset.mem_Ioc] at ht; omega) ω).1
  have hE1nn : ∀ ω, 0 ≤ E1 ω := fun ω => Finset.sum_nonneg fun t ht =>
    (hr t (by rw [Finset.mem_Ioc] at ht; omega) ω).1
  have hE1le : ∀ ω, E1 ω ≤ α1 * M.pmax := by
    intro ω
    calc E1 ω ≤ ∑ t ∈ Finset.Ioc 0 α1, M.pmax := Finset.sum_le_sum fun t ht =>
          (hr t (by rw [Finset.mem_Ioc] at ht; omega) ω).2
      _ = α1 * M.pmax := by simp
  have hEm : ∀ k, Measurable (E k) := fun k => Finset.measurable_sum _ fun t ht =>
    hrm t (by rw [Finset.mem_Ioc] at ht; omega)
  have hE1m : Measurable E1 := Finset.measurable_sum _ fun t ht =>
    hrm t (by rw [Finset.mem_Ioc] at ht; omega)
  have hpt : ∀ ω, cumRegret M x p T ω ≤ E1 ω + ∑ k ∈ Finset.Icc 2 n, E k ω := by
    intro ω
    have h1 : cumRegret M x p T ω = ∑ t ∈ Finset.Ioc 0 T, perRegret M (x t ω) (p t ω) := by
      unfold cumRegret; rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    rw [h1, hE1, hE]
    simp only
    rw [← sum_decomp α1 α2 (fun t => perRegret M (x t ω) (p t ω)) n hn1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hnT)
      fun t ht _ => (hr t (by rw [Finset.mem_Ioc] at ht; omega) ω).1
  -- episode bounds from the child lemma
  have hchildk : ∀ k ∈ Finset.Icc 2 n,
      ∫⁻ ω, ENNReal.ofReal (E k ω) ∂P ≤
        ENNReal.ofReal (max 0 (C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
          (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3))) +
        ENNReal.ofReal (4 * M.pmax * L) * (((2 ^ (k - 2) * α2 : ℕ) : ℝ≥0∞) *
          ∫⁻ ω, ENNReal.ofReal (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk2 := hk.1
    have hT0 : 1 ≤ 2 ^ (k - 2) * α2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hlen : epLen α1 α2 k = 2 ^ (k - 2) * α2 := by simp [epLen]; omega
    have hc := hchild Ω mΩ P 𝒢 x z p hEnv (epEnd α1 α2 (k - 1)) (2 ^ (k - 2) * α2) hT0
      (thetaHat M α1 α2 est x z p (k - 1))
      (thetaHat_meas M α1 α2 P 𝒢 x z p hEnv est hest (k - 1) (by omega))
      (fun ω => (hest (k - 1)).2 _)
      (fun ω => by
        obtain ⟨j, hj⟩ := (hrun ω).2 k hk2
        rw [hlen] at hj
        exact ⟨j, hj⟩)
    have hset : Finset.Icc (epEnd α1 α2 (k - 1) + 1) (epEnd α1 α2 (k - 1) + 2 ^ (k - 2) * α2) =
        Finset.Ioc (epEnd α1 α2 (k - 1)) (epEnd α1 α2 k) := by
      rw [Finset.Icc_add_one_left_eq_Ioc, ← epEnd_eq α1 α2 k hk2]
    rw [hset] at hc
    have hmul : ENNReal.ofReal (4 * M.pmax * L * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
        ∫⁻ ω, ENNReal.ofReal (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P =
        ENNReal.ofReal (4 * M.pmax * L) * (((2 ^ (k - 2) * α2 : ℕ) : ℝ≥0∞) *
          ∫⁻ ω, ENNReal.ofReal (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P) := by
      have h4 : 0 ≤ 4 * M.pmax * (L : ℝ) := by have := hp.le; positivity
      rw [ENNReal.ofReal_mul h4, ENNReal.ofReal_natCast, mul_assoc]
    refine le_trans hc ?_
    rw [hmul]
    exact add_le_add_left (ENNReal.ofReal_le_ofReal (le_max_right _ _)) _
  calc ∫⁻ ω, ENNReal.ofReal (cumRegret M x p T ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (E1 ω) + ∑ k ∈ Finset.Icc 2 n, ENNReal.ofReal (E k ω)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hEnn k ω,
          ← ENNReal.ofReal_add (hE1nn ω) (Finset.sum_nonneg fun k _ => hEnn k ω)]
        exact ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ∫⁻ ω, ENNReal.ofReal (E1 ω) ∂P + ∑ k ∈ Finset.Icc 2 n, ∫⁻ ω, ENNReal.ofReal (E k ω) ∂P := by
        rw [lintegral_add_left hE1m.ennreal_ofReal,
          lintegral_finsetSum _ fun k _ => (hEm k).ennreal_ofReal]
    _ ≤ ENNReal.ofReal (α1 * M.pmax) + ∑ k ∈ Finset.Icc 2 n,
          (ENNReal.ofReal (max 0 (C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
            (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3))) +
          ENNReal.ofReal (4 * M.pmax * L) * (((2 ^ (k - 2) * α2 : ℕ) : ℝ≥0∞) *
            ∫⁻ ω, ENNReal.ofReal (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P)) := by
        gcongr with k hk
        · calc ∫⁻ ω, ENNReal.ofReal (E1 ω) ∂P ≤ ∫⁻ _ω, ENNReal.ofReal (α1 * M.pmax) ∂P :=
                lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hE1le ω)
            _ = ENNReal.ofReal (α1 * M.pmax) := by simp
        · exact hchildk k hk
    _ = ENNReal.ofReal (α1 * M.pmax + ∑ k ∈ Finset.Icc 2 n,
          max 0 (C3 * Real.log (C2 * ((2 ^ (k - 2) * α2 : ℕ) : ℝ)) *
            (((2 ^ (k - 2) * α2 : ℕ) : ℝ)) ^ ((2 : ℝ) / 3))) +
        ENNReal.ofReal (4 * M.pmax * L) * ∑ k ∈ Finset.Icc 2 n,
          ((2 ^ (k - 2) * α2 : ℕ) : ℝ≥0∞) *
            ∫⁻ ω, ENNReal.ofReal (l1 (thetaHat M α1 α2 est x z p (k - 1) ω - M.θ0)) ∂P := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun k _ => le_max_left _ _),
          ENNReal.ofReal_sum_of_nonneg fun k _ => le_max_left _ _, add_assoc]
    _ ≤ _ := by
        gcongr
        refine final_real α1 α2 hα2 M.pmax C2 C3 hp hC2 hC3 T n hT fun hn2 => ?_
        have h := hnprev hn2
        have hE' := epEnd_eq α1 α2 n hn2
        have hE'' : epEnd α1 α2 n = α1 + α2 * (2 ^ (n - 1) - 1) := rfl
        have h2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
          rw [← pow_succ']; congr 1; omega
        have h3 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
        have h4 : epEnd α1 α2 (n - 1) = α1 + α2 * (2 ^ (n - 2) - 1) := by
          simp only [epEnd]; congr 3
        rw [h4] at h
        have h5 : α2 * (2 ^ (n - 2) - 1) + α2 = 2 ^ (n - 2) * α2 := by
          obtain ⟨q, hq⟩ : ∃ q, 2 ^ (n - 2) = q + 1 := ⟨2 ^ (n - 2) - 1, by omega⟩
          rw [hq, Nat.add_sub_cancel]; ring
        omega
