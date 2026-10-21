-- Prove2me | solution 1 for HumanMachine.Accuracy.corollary_2_value
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:10:53.61198+00:00
-- url     : https://prove2.me/submissions/dd9f09a2-3679-45ba-b14a-7113d9677499

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

set_option autoImplicit false
open HumanMachine.Accuracy

noncomputable def klt (x q : ℝ) : ℝ :=
  x * Real.log x + (1 - x) * Real.log (1 - x) - x * Real.log q - (1 - x) * Real.log (1 - q)

lemma klt_self (x : ℝ) : klt x x = 0 := by unfold klt; ring

lemma klt_symm (x q : ℝ) : klt (1 - x) (1 - q) = klt x q := by
  unfold klt; simp only [sub_sub_cancel]; ring

lemma klt_nonneg (x r : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ klt x r := by
  have key : ∀ y s : ℝ, 0 ≤ y → 0 < s → y * (Real.log s - Real.log y) ≤ s - y := by
    intro y s hy hs
    rcases hy.eq_or_lt with h | h
    · subst h; simp [hs.le]
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hs h)
      rw [Real.log_div hs.ne' h.ne'] at h1
      calc y * (Real.log s - Real.log y) ≤ y * (s / y - 1) := mul_le_mul_of_nonneg_left h1 hy
        _ = s - y := by field_simp
  have h1 := key x r hx0 hr0
  have h2 := key (1 - x) (1 - r) (by linarith) (by linarith)
  unfold klt
  nlinarith

lemma gibbs_id (lam E x q : ℝ) (hlam : 0 < lam) (hE0 : 0 < E) (hE : Real.log E = 1 / lam)
    (hq0 : 0 < q) (hq1 : q < 1) :
    x - lam * klt x q = lam * Real.log (1 - q + q * E)
      - lam * klt x (q * E / (1 - q + q * E)) := by
  have h1q : 0 < 1 - q := by linarith
  have hqE : 0 < q * E := mul_pos hq0 hE0
  have hY : 0 < 1 - q + q * E := by linarith
  have hr : Real.log (q * E / (1 - q + q * E))
      = Real.log q + 1 / lam - Real.log (1 - q + q * E) := by
    rw [Real.log_div hqE.ne' hY.ne', Real.log_mul hq0.ne' hE0.ne', hE]
  have hr1 : Real.log (1 - q * E / (1 - q + q * E))
      = Real.log (1 - q) - Real.log (1 - q + q * E) := by
    have : 1 - q * E / (1 - q + q * E) = (1 - q) / (1 - q + q * E) := by field_simp; ring
    rw [this, Real.log_div h1q.ne' hY.ne']
  unfold klt
  rw [hr, hr1]
  field_simp
  ring

lemma gibbs_r_mem (E q : ℝ) (hE0 : 0 < E) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < q * E / (1 - q + q * E) ∧ q * E / (1 - q + q * E) < 1 := by
  have h1q : 0 < 1 - q := by linarith
  have hqE : 0 < q * E := mul_pos hq0 hE0
  have hY : 0 < 1 - q + q * E := by linarith
  refine ⟨div_pos hqE hY, ?_⟩
  rw [div_lt_one hY]; linarith

lemma gibbs_le (lam E x q : ℝ) (hlam : 0 < lam) (hE0 : 0 < E) (hE : Real.log E = 1 / lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    x - lam * klt x q ≤ lam * Real.log (1 - q + q * E) := by
  rw [gibbs_id lam E x q hlam hE0 hE hq0 hq1]
  obtain ⟨h0, h1⟩ := gibbs_r_mem E q hE0 hq0 hq1
  have := klt_nonneg x _ hx0 hx1 h0 h1
  nlinarith

lemma gibbs_eq (lam E q : ℝ) (hlam : 0 < lam) (hE0 : 0 < E) (hE : Real.log E = 1 / lam)
    (hq0 : 0 < q) (hq1 : q < 1) :
    q * E / (1 - q + q * E) - lam * klt (q * E / (1 - q + q * E)) q
      = lam * Real.log (1 - q + q * E) := by
  rw [gibbs_id lam E _ q hlam hE0 hE hq0 hq1, klt_self]; ring

lemma value_eq (lam μ pg pb p : ℝ) (hp : p = μ * pg + (1 - μ) * pb) :
    HumanMachine.Alone.value lam μ pg pb =
      μ * (pg - lam * klt pg p) + (1 - μ) * ((1 - pb) - lam * klt pb p) := by
  subst hp
  simp only [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
    HumanMachine.Alone.choiceProb, Real.binEntropy, Real.log_inv, klt]
  ring

lemma value_le_F (lam E μ pg pb p : ℝ) (hlam : 0 < lam) (hE0 : 0 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1)
    (hp : p = μ * pg + (1 - μ) * pb) :
    HumanMachine.Alone.value lam μ pg pb ≤
      lam * (μ * Real.log (1 - p + p * E) + (1 - μ) * Real.log (p + (1 - p) * E)) := by
  have hnμ : 0 ≤ 1 - μ := by linarith
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by rw [hp]; nlinarith
  rcases hp0.eq_or_lt with h0 | h0
  · -- p = 0
    have hp0' : p = 0 := h0.symm
    have ha : μ * pg = 0 := by
      have := mul_nonneg hμ0 hpg0; have := mul_nonneg hnμ hpb0; linarith
    have hb : (1 - μ) * pb = 0 := by
      have := mul_nonneg hμ0 hpg0; have := mul_nonneg hnμ hpb0; linarith
    have hH1 : μ * Real.binEntropy pg = 0 := by
      rcases mul_eq_zero.mp ha with h | h <;> simp [h]
    have hH2 : (1 - μ) * Real.binEntropy pb = 0 := by
      rcases mul_eq_zero.mp hb with h | h <;> simp [h]
    have hH0 : Real.binEntropy (μ * pg + (1 - μ) * pb) = 0 := by
      rw [← hp, hp0']; simp
    have hR : lam * (μ * Real.log (1 - p + p * E) + (1 - μ) * Real.log (p + (1 - p) * E))
        = 1 - μ := by
      rw [hp0']; simp; rw [hE]; field_simp
    rw [hR]
    simp only [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
      HumanMachine.Alone.choiceProb]
    rw [hH0]
    nlinarith
  rcases hp1.eq_or_lt with h1 | h1
  · -- p = 1
    have hp1' : p = 1 := h1
    have ha : μ * (1 - pg) = 0 := by
      have := mul_nonneg hμ0 (sub_nonneg.mpr hpg1)
      have := mul_nonneg hnμ (sub_nonneg.mpr hpb1)
      nlinarith
    have hb : (1 - μ) * (1 - pb) = 0 := by
      have := mul_nonneg hμ0 (sub_nonneg.mpr hpg1)
      have := mul_nonneg hnμ (sub_nonneg.mpr hpb1)
      nlinarith
    have hH1 : μ * Real.binEntropy pg = 0 := by
      rcases mul_eq_zero.mp ha with h | h
      · simp [h]
      · have : pg = 1 := by linarith
        simp [this]
    have hH2 : (1 - μ) * Real.binEntropy pb = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · simp [h]
      · have : pb = 1 := by linarith
        simp [this]
    have hH0 : Real.binEntropy (μ * pg + (1 - μ) * pb) = 0 := by
      rw [← hp, hp1']; simp
    have hR : lam * (μ * Real.log (1 - p + p * E) + (1 - μ) * Real.log (p + (1 - p) * E))
        = μ := by
      rw [hp1']; simp; rw [hE]; field_simp
    rw [hR]
    simp only [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
      HumanMachine.Alone.choiceProb]
    rw [hH0]
    nlinarith
  · -- 0 < p < 1
    have e := value_eq lam μ pg pb p hp
    have g1 := gibbs_le lam E pg p hlam hE0 hE hpg0 hpg1 h0 h1
    have g2 := gibbs_le lam E (1 - pb) (1 - p) hlam hE0 hE (by linarith) (by linarith)
      (by linarith) (by linarith)
    rw [klt_symm] at g2
    have e2 : 1 - (1 - p) = p := by ring
    rw [e2] at g2
    rw [e]
    have m1 := mul_le_mul_of_nonneg_left g1 hμ0
    have m2 := mul_le_mul_of_nonneg_left g2 hnμ
    nlinarith

lemma log_tan (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.log a ≤ Real.log b + (a - b) / b := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have : (a - b) / b = a / b - 1 := by field_simp
  linarith

lemma F_tan (lam E μ p a1 a2 : ℝ) (hlam : 0 < lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hY1 : 0 < 1 - p + p * E) (hY2 : 0 < p + (1 - p) * E) :
    lam * (μ * Real.log (1 - p + p * E) + (1 - μ) * Real.log (p + (1 - p) * E)) ≤
      lam * (μ * (Real.log a1 + ((1 - p + p * E) - a1) / a1)
        + (1 - μ) * (Real.log a2 + ((p + (1 - p) * E) - a2) / a2)) := by
  have h1 := log_tan _ _ hY1 ha1
  have h2 := log_tan _ _ hY2 ha2
  have hnμ : 0 ≤ 1 - μ := by linarith
  apply mul_le_mul_of_nonneg_left _ hlam.le
  have m1 := mul_le_mul_of_nonneg_left h1 hμ0
  have m2 := mul_le_mul_of_nonneg_left h2 hnμ
  linarith

lemma Y_pos (E p : ℝ) (hE : 1 < E) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 < 1 - p + p * E ∧ 0 < p + (1 - p) * E := by
  constructor <;> nlinarith

/-- Regime 1 upper bound -/
lemma ub_R1 (lam E μ pg pb : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hμE : μ * (E + 1) ≤ 1)
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1) :
    HumanMachine.Alone.value lam μ pg pb ≤ 1 - μ := by
  have hE0 : 0 < E := by linarith
  set p := μ * pg + (1 - μ) * pb with hp
  have hp0 : 0 ≤ p := by rw [hp]; have := mul_nonneg hμ0 hpg0; have := mul_nonneg (sub_nonneg.mpr hμ1) hpb0; linarith
  have hp1 : p ≤ 1 := by rw [hp]; nlinarith
  obtain ⟨hY1, hY2⟩ := Y_pos E p hE1 hp0 hp1
  refine (value_le_F lam E μ pg pb p hlam hE0 hE hμ0 hμ1 hpg0 hpg1 hpb0 hpb1 hp).trans ?_
  refine (F_tan lam E μ p 1 E hlam hμ0 hμ1 one_pos hE0 hY1 hY2).trans ?_
  have key : lam * (μ * (Real.log 1 + ((1 - p + p * E) - 1) / 1)
        + (1 - μ) * (Real.log E + ((p + (1 - p) * E) - E) / E))
      = (1 - μ) + lam * p * (E - 1) * (μ * (E + 1) - 1) / E := by
    rw [hE, Real.log_one]; field_simp; ring
  rw [key]
  have : lam * p * (E - 1) * (μ * (E + 1) - 1) / E ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hE0.le
    apply mul_nonpos_of_nonneg_of_nonpos
    · have : 0 ≤ E - 1 := by linarith
      positivity
    · linarith
  linarith

/-- Regime 3 upper bound -/
lemma ub_R3 (lam E μ pg pb : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hμE : E ≤ μ * (E + 1))
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1) :
    HumanMachine.Alone.value lam μ pg pb ≤ μ := by
  have hE0 : 0 < E := by linarith
  set p := μ * pg + (1 - μ) * pb with hp
  have hp0 : 0 ≤ p := by rw [hp]; have := mul_nonneg hμ0 hpg0; have := mul_nonneg (sub_nonneg.mpr hμ1) hpb0; linarith
  have hp1 : p ≤ 1 := by rw [hp]; nlinarith
  obtain ⟨hY1, hY2⟩ := Y_pos E p hE1 hp0 hp1
  refine (value_le_F lam E μ pg pb p hlam hE0 hE hμ0 hμ1 hpg0 hpg1 hpb0 hpb1 hp).trans ?_
  refine (F_tan lam E μ p E 1 hlam hμ0 hμ1 hE0 one_pos hY1 hY2).trans ?_
  have key : lam * (μ * (Real.log E + ((1 - p + p * E) - E) / E)
        + (1 - μ) * (Real.log 1 + ((p + (1 - p) * E) - 1) / 1))
      = μ + lam * (1 - p) * (E - 1) * (E - μ * (E + 1)) / E := by
    rw [hE, Real.log_one]; field_simp; ring
  rw [key]
  have : lam * (1 - p) * (E - 1) * (E - μ * (E + 1)) / E ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hE0.le
    apply mul_nonpos_of_nonneg_of_nonpos
    · have : 0 ≤ E - 1 := by linarith
      have : 0 ≤ 1 - p := by linarith
      positivity
    · linarith
  linarith

/-- Regime 2 upper bound -/
lemma ub_R2 (lam E μ pg pb : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1) :
    HumanMachine.Alone.value lam μ pg pb ≤
      lam * (Real.log (E + 1) - Real.binEntropy μ) := by
  have hE0 : 0 < E := by linarith
  set p := μ * pg + (1 - μ) * pb with hp
  have hp0 : 0 ≤ p := by rw [hp]; have := mul_nonneg hμ0.le hpg0; have := mul_nonneg (sub_nonneg.mpr hμ1.le) hpb0; linarith
  have hp1 : p ≤ 1 := by rw [hp]; nlinarith
  obtain ⟨hY1, hY2⟩ := Y_pos E p hE1 hp0 hp1
  have hn : 0 < 1 - μ := by linarith
  have hEp : 0 < E + 1 := by linarith
  refine (value_le_F lam E μ pg pb p hlam hE0 hE hμ0.le hμ1.le hpg0 hpg1 hpb0 hpb1 hp).trans ?_
  refine (F_tan lam E μ p (μ * (E + 1)) ((1 - μ) * (E + 1)) hlam hμ0.le hμ1.le
    (by positivity) (by positivity) hY1 hY2).trans ?_
  have key : μ * (Real.log (μ * (E + 1)) + ((1 - p + p * E) - μ * (E + 1)) / (μ * (E + 1)))
        + (1 - μ) * (Real.log ((1 - μ) * (E + 1))
          + ((p + (1 - p) * E) - (1 - μ) * (E + 1)) / ((1 - μ) * (E + 1)))
      = Real.log (E + 1) - Real.binEntropy μ := by
    have e1 : ((1 - p + p * E) - μ * (E + 1)) / (μ * (E + 1)) * μ
        + ((p + (1 - p) * E) - (1 - μ) * (E + 1)) / ((1 - μ) * (E + 1)) * (1 - μ) = 0 := by
      field_simp; ring
    rw [Real.log_mul hμ0.ne' hEp.ne', Real.log_mul hn.ne' hEp.ne']
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    linarith
  rw [key]

lemma VStar_eq (lam μ T pg0 pb0 : ℝ)
    (hub : ∀ qg ∈ Set.Icc (0 : ℝ) 1, ∀ qb ∈ Set.Icc (0 : ℝ) 1,
      HumanMachine.Alone.value lam μ qg qb ≤ T)
    (hg : pg0 ∈ Set.Icc (0 : ℝ) 1) (hb : pb0 ∈ Set.Icc (0 : ℝ) 1)
    (hval : HumanMachine.Alone.value lam μ pg0 pb0 = T) :
    VStar lam μ = T := by
  have hex : ∃ q : ℝ × ℝ, HumanMachine.Alone.IsOptimal lam μ q.1 q.2 :=
    ⟨(pg0, pb0), hg, hb, fun qg hqg qb hqb => by rw [← hval] at hub; simpa [hval] using hub qg hqg qb hqb⟩
  have h : HumanMachine.Alone.IsOptimal lam μ (optPair lam μ).1 (optPair lam μ).2 :=
    Classical.epsilon_spec hex
  obtain ⟨h1, h2, hopt⟩ := h
  apply le_antisymm
  · exact hub _ h1 _ h2
  · have := hopt pg0 hg pb0 hb
    unfold VStar
    linarith

theorem solution (lam μ : ℝ) (hlam : 0 < lam) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (μ ≤ HumanMachine.Alone.muLow lam → VStar lam μ = 1 - μ) ∧
      (HumanMachine.Alone.muLow lam < μ → μ < HumanMachine.Alone.muHigh lam →
        VStar lam μ = lam * (Real.log (Real.exp (1 / lam) + 1) - Real.binEntropy μ)) ∧
      (HumanMachine.Alone.muHigh lam ≤ μ → VStar lam μ = μ) := by
  obtain ⟨hμ0, hμ1⟩ := hμ
  set E := Real.exp (1 / lam) with hEdef
  have hE1 : 1 < E := by
    rw [hEdef]; calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < _ := Real.exp_lt_exp.mpr (by positivity)
  have hE0 : 0 < E := by linarith
  have hEp : 0 < E + 1 := by linarith
  have hE : Real.log E = 1 / lam := Real.log_exp _
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hμE : μ * (E + 1) ≤ 1 := by
      unfold HumanMachine.Alone.muLow at h; rw [← hEdef] at h
      exact (le_div_iff₀ hEp).mp h
    refine VStar_eq lam μ _ 0 0 ?_ (by simp) (by simp) ?_
    · intro qg hqg qb hqb
      exact ub_R1 lam E μ qg qb hlam hE1 hE hμ0 hμ1 hμE hqg.1 hqg.2 hqb.1 hqb.2
    · simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
        HumanMachine.Alone.choiceProb]
  · intro hlo hhi
    have h1 : 1 < μ * (E + 1) := by
      unfold HumanMachine.Alone.muLow at hlo; rw [← hEdef] at hlo
      exact (div_lt_iff₀ hEp).mp hlo
    have h2 : μ * (E + 1) < E := by
      unfold HumanMachine.Alone.muHigh at hhi; rw [← hEdef] at hhi
      exact (lt_div_iff₀ hEp).mp hhi
    have hμ0' : 0 < μ := by
      by_contra hcon
      have : μ = 0 := le_antisymm (not_lt.mp hcon) hμ0
      rw [this] at h1; linarith
    have hμ1' : μ < 1 := by
      by_contra hcon
      have : 1 ≤ μ := not_lt.mp hcon
      nlinarith
    -- optimal pair
    set q := (μ * (E + 1) - 1) / (E - 1) with hq
    have hE1' : 0 < E - 1 := by linarith
    have hq0 : 0 < q := div_pos (by linarith) hE1'
    have hq1 : q < 1 := by rw [hq, div_lt_one hE1']; linarith
    have hY1 : 1 - q + q * E = μ * (E + 1) := by
      rw [hq]; field_simp; ring
    have hY2 : q + (1 - q) * E = (1 - μ) * (E + 1) := by
      rw [hq]; field_simp; ring
    obtain ⟨hr0, hr1⟩ := gibbs_r_mem E q hE0 hq0 hq1
    have hq' : 0 < 1 - q := by linarith
    obtain ⟨hs0, hs1⟩ := gibbs_r_mem E (1 - q) hE0 hq' (by linarith)
    obtain ⟨pg, hpg⟩ : ∃ pg, pg = q * E / (1 - q + q * E) := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s, s = (1 - q) * E / (1 - (1 - q) + (1 - q) * E) := ⟨_, rfl⟩
    rw [← hpg] at hr0 hr1
    rw [← hs] at hs0 hs1
    have hpb : 1 - s = q / (q + (1 - q) * E) := by
      rw [hs]
      have : 1 - (1 - q) + (1 - q) * E = q + (1 - q) * E := by ring
      rw [this]
      have hpos : 0 < q + (1 - q) * E := by nlinarith
      field_simp; ring
    have hcons : μ * pg + (1 - μ) * (1 - s) = q := by
      rw [hpg, hpb, hY1, hY2]
      have hμn : (1 - μ) ≠ 0 := by linarith
      field_simp
      try (rw [hq]; field_simp)
      try ring
    have hval : HumanMachine.Alone.value lam μ pg (1 - s) =
        lam * (Real.log (E + 1) - Real.binEntropy μ) := by
      rw [value_eq lam μ pg (1 - s) q hcons.symm]
      have g1 := gibbs_eq lam E q hlam hE0 hE hq0 hq1
      have g2 := gibbs_eq lam E (1 - q) hlam hE0 hE hq' (by linarith)
      have e2 : 1 - (1 - q) + (1 - q) * E = q + (1 - q) * E := by ring
      rw [← hs] at g2
      rw [e2] at g2
      rw [← hpg] at g1
      have hk : klt (1 - s) q = klt s (1 - q) := by
        have := klt_symm s (1 - q)
        rw [sub_sub_cancel] at this
        exact this
      rw [hk, sub_sub_cancel, g1, g2, hY1, hY2, Real.log_mul hμ0'.ne' hEp.ne',
        Real.log_mul (by linarith : (1 - μ) ≠ 0) hEp.ne']
      unfold Real.binEntropy
      rw [Real.log_inv, Real.log_inv]
      ring
    exact VStar_eq lam μ _ pg (1 - s)
      (fun qg hqg qb hqb => ub_R2 lam E μ qg qb hlam hE1 hE hμ0' hμ1' hqg.1 hqg.2 hqb.1 hqb.2)
      ⟨hr0.le, hr1.le⟩ ⟨by linarith, by linarith⟩ hval
  · intro h
    have hμE : E ≤ μ * (E + 1) := by
      unfold HumanMachine.Alone.muHigh at h; rw [← hEdef] at h
      exact (div_le_iff₀ hEp).mp h
    refine VStar_eq lam μ _ 1 1 ?_ (by simp) (by simp) ?_
    · intro qg hqg qb hqb
      exact ub_R3 lam E μ qg qb hlam hE1 hE hμ0 hμ1 hμE hqg.1 hqg.2 hqb.1 hqb.2
    · simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
        HumanMachine.Alone.choiceProb]
