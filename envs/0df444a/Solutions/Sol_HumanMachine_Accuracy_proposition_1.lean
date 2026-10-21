-- Prove2me | solution 1 for HumanMachine.Accuracy.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:21:10.153142+00:00
-- url     : https://prove2.me/submissions/4e540b69-fc73-4382-b575-b75e0682d50a

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
import Definitions.Def_HumanMachine_Accuracy_Machine

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


lemma log_tan_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : Real.log a = Real.log b + (a - b) / b) : a = b := by
  by_contra hne
  have hne' : a / b ≠ 1 := by
    intro h1; apply hne; rw [div_eq_one_iff_eq hb.ne'] at h1; exact h1
  have h1 := Real.log_lt_sub_one_of_pos (div_pos ha hb) hne'
  rw [Real.log_div ha.ne' hb.ne'] at h1
  have e : (a - b) / b = a / b - 1 := by field_simp
  linarith

lemma klt_eq_zero (x r : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (h : klt x r = 0) : x = r := by
  by_contra hne
  have key : ∀ y s : ℝ, 0 ≤ y → 0 < s → y * (Real.log s - Real.log y) ≤ s - y := by
    intro y s hy hs
    rcases hy.eq_or_lt with h | h
    · subst h; simp [hs.le]
    · have h1 := Real.log_le_sub_one_of_pos (div_pos hs h)
      rw [Real.log_div hs.ne' h.ne'] at h1
      calc y * (Real.log s - Real.log y) ≤ y * (s / y - 1) := mul_le_mul_of_nonneg_left h1 hy
        _ = s - y := by field_simp
  have keyS : ∀ y s : ℝ, 0 < y → 0 < s → y ≠ s → y * (Real.log s - Real.log y) < s - y := by
    intro y s hy hs hne
    have h1 := Real.log_lt_sub_one_of_pos (div_pos hs hy) (by
      intro h; apply hne; rw [div_eq_one_iff_eq hy.ne'] at h; exact h.symm)
    rw [Real.log_div hs.ne' hy.ne'] at h1
    calc y * (Real.log s - Real.log y) < y * (s / y - 1) := mul_lt_mul_of_pos_left h1 hy
      _ = s - y := by field_simp
  rcases hx0.eq_or_lt with h0 | h0
  · subst h0
    have : Real.log (1 - r) < 0 := Real.log_neg (by linarith) (by linarith)
    have e : klt 0 r = -Real.log (1 - r) := by unfold klt; simp
    linarith
  rcases hx1.eq_or_lt with h1 | h1
  · subst h1
    have : Real.log r < 0 := Real.log_neg hr0 hr1
    have e : klt 1 r = -Real.log r := by unfold klt; simp
    linarith
  have k1 := key (1 - x) (1 - r) (by linarith) (by linarith)
  have k2 := keyS x r h0 hr0 hne
  unfold klt at h
  nlinarith

lemma chain_eq (lam E μ p a1 a2 T V : ℝ) (hlam : 0 < lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hY1 : 0 < 1 - p + p * E) (hY2 : 0 < p + (1 - p) * E)
    (hVF : V ≤ lam * (μ * Real.log (1 - p + p * E) + (1 - μ) * Real.log (p + (1 - p) * E)))
    (htan : lam * (μ * (Real.log a1 + ((1 - p + p * E) - a1) / a1)
        + (1 - μ) * (Real.log a2 + ((p + (1 - p) * E) - a2) / a2)) ≤ T)
    (hV : V = T) :
    (0 < μ → 1 - p + p * E = a1) ∧ (0 < 1 - μ → p + (1 - p) * E = a2) := by
  have d1 := log_tan _ _ hY1 ha1
  have d2 := log_tan _ _ hY2 ha2
  have hnμ : 0 ≤ 1 - μ := by linarith
  set u1 := Real.log a1 + ((1 - p + p * E) - a1) / a1 - Real.log (1 - p + p * E) with hu1
  set u2 := Real.log a2 + ((p + (1 - p) * E) - a2) / a2 - Real.log (p + (1 - p) * E) with hu2
  have hu1' : 0 ≤ u1 := by rw [hu1]; linarith
  have hu2' : 0 ≤ u2 := by rw [hu2]; linarith
  have s1 : 0 ≤ μ * u1 := mul_nonneg hμ0 hu1'
  have s2 : 0 ≤ (1 - μ) * u2 := mul_nonneg hnμ hu2'
  have hsum : lam * (μ * u1 + (1 - μ) * u2) ≤ 0 := by
    have : lam * (μ * u1 + (1 - μ) * u2) =
      lam * (μ * (Real.log a1 + ((1 - p + p * E) - a1) / a1)
        + (1 - μ) * (Real.log a2 + ((p + (1 - p) * E) - a2) / a2))
      - lam * (μ * Real.log (1 - p + p * E) + (1 - μ) * Real.log (p + (1 - p) * E)) := by
      rw [hu1, hu2]; ring
    rw [this]; linarith
  have hsum' : μ * u1 + (1 - μ) * u2 ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_pos hlam hcon
    linarith
  have e1 : μ * u1 = 0 := by linarith
  have e2 : (1 - μ) * u2 = 0 := by linarith
  constructor
  · intro hμ
    have : u1 = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hμ.ne'
      · exact h
    apply log_tan_eq _ _ hY1 ha1
    rw [hu1] at this; linarith
  · intro hμ
    have : u2 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h hμ.ne'
      · exact h
    apply log_tan_eq _ _ hY2 ha2
    rw [hu2] at this; linarith

lemma tan_R1 (lam E μ p : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hp0 : 0 ≤ p) (hμE : μ * (E + 1) ≤ 1) :
    lam * (μ * (Real.log 1 + ((1 - p + p * E) - 1) / 1)
        + (1 - μ) * (Real.log E + ((p + (1 - p) * E) - E) / E)) ≤ 1 - μ := by
  have hE0 : 0 < E := by linarith
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

lemma tan_R3 (lam E μ p : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hp1 : p ≤ 1) (hμE : E ≤ μ * (E + 1)) :
    lam * (μ * (Real.log E + ((1 - p + p * E) - E) / E)
        + (1 - μ) * (Real.log 1 + ((p + (1 - p) * E) - 1) / 1)) ≤ μ := by
  have hE0 : 0 < E := by linarith
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

lemma tan_R2 (lam E μ p : ℝ) (hE1 : 1 < E) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    lam * (μ * (Real.log (μ * (E + 1)) + ((1 - p + p * E) - μ * (E + 1)) / (μ * (E + 1)))
        + (1 - μ) * (Real.log ((1 - μ) * (E + 1))
          + ((p + (1 - p) * E) - (1 - μ) * (E + 1)) / ((1 - μ) * (E + 1))))
      = lam * (Real.log (E + 1) - Real.binEntropy μ) := by
  have hE0 : 0 < E := by linarith
  have hn : 0 < 1 - μ := by linarith
  have hEp : 0 < E + 1 := by linarith
  congr 1
  have e1 : ((1 - p + p * E) - μ * (E + 1)) / (μ * (E + 1)) * μ
      + ((p + (1 - p) * E) - (1 - μ) * (E + 1)) / ((1 - μ) * (E + 1)) * (1 - μ) = 0 := by
    field_simp; ring
  rw [Real.log_mul hμ0.ne' hEp.ne', Real.log_mul hn.ne' hEp.ne']
  unfold Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  linarith

lemma p_facts (μ pg pb p : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1)
    (hp : p = μ * pg + (1 - μ) * pb) : 0 ≤ p ∧ p ≤ 1 := by
  have := mul_nonneg hμ0 hpg0
  have := mul_nonneg (sub_nonneg.mpr hμ1) hpb0
  constructor
  · rw [hp]; linarith
  · rw [hp]; nlinarith

lemma reg1_eq (lam E μ pg pb : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hμE : μ * (E + 1) ≤ 1)
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1)
    (hv : HumanMachine.Alone.value lam μ pg pb = 1 - μ) :
    μ * pg + (1 - μ) * (1 - pb) = 1 - μ := by
  have hE0 : 0 < E := by linarith
  obtain ⟨hp0, hp1⟩ := p_facts μ pg pb _ hμ0 hμ1 hpg0 hpg1 hpb0 hpb1 rfl
  set p := μ * pg + (1 - μ) * pb with hp
  obtain ⟨hY1, hY2⟩ := Y_pos E p hE1 hp0 hp1
  have hn : 0 < 1 - μ := by nlinarith
  have hVF := value_le_F lam E μ pg pb p hlam hE0 hE hμ0 hμ1 hpg0 hpg1 hpb0 hpb1 hp
  have htan := tan_R1 lam E μ p hlam hE1 hE hp0 hμE
  have hch := chain_eq lam E μ p 1 E (1 - μ) _ hlam hμ0 hμ1 one_pos hE0 hY1 hY2 hVF htan hv
  have hY := hch.2 hn
  have hp' : p * (E - 1) = 0 := by nlinarith
  have hp00 : p = 0 := (mul_eq_zero.mp hp').resolve_right (by linarith)
  have ha : μ * pg = 0 := by
    have := mul_nonneg hμ0 hpg0; have := mul_nonneg hn.le hpb0; linarith
  have hb : (1 - μ) * pb = 0 := by
    have := mul_nonneg hμ0 hpg0; have := mul_nonneg hn.le hpb0; linarith
  nlinarith

lemma reg3_eq (lam E μ pg pb : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (hμE : E ≤ μ * (E + 1))
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1)
    (hv : HumanMachine.Alone.value lam μ pg pb = μ) :
    μ * pg + (1 - μ) * (1 - pb) = μ := by
  have hE0 : 0 < E := by linarith
  obtain ⟨hp0, hp1⟩ := p_facts μ pg pb _ hμ0 hμ1 hpg0 hpg1 hpb0 hpb1 rfl
  set p := μ * pg + (1 - μ) * pb with hp
  obtain ⟨hY1, hY2⟩ := Y_pos E p hE1 hp0 hp1
  have hμp : 0 < μ := by nlinarith
  have hn : 0 ≤ 1 - μ := by linarith
  have hVF := value_le_F lam E μ pg pb p hlam hE0 hE hμ0 hμ1 hpg0 hpg1 hpb0 hpb1 hp
  have htan := tan_R3 lam E μ p hlam hE1 hE hp1 hμE
  have hch := chain_eq lam E μ p E 1 μ _ hlam hμ0 hμ1 hE0 one_pos hY1 hY2 hVF htan hv
  have hY := hch.1 hμp
  have hp' : (1 - p) * (E - 1) = 0 := by nlinarith
  have hp00 : p = 1 := by
    have := (mul_eq_zero.mp hp').resolve_right (by linarith)
    linarith
  have ha : μ * (1 - pg) = 0 := by
    have := mul_nonneg hμ0 (sub_nonneg.mpr hpg1); have := mul_nonneg hn (sub_nonneg.mpr hpb1)
    nlinarith
  have hb : (1 - μ) * (1 - pb) = 0 := by
    have := mul_nonneg hμ0 (sub_nonneg.mpr hpg1); have := mul_nonneg hn (sub_nonneg.mpr hpb1)
    nlinarith
  nlinarith

lemma reg2_eq (lam E μ pg pb : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (h1 : 1 < μ * (E + 1)) (h2 : μ * (E + 1) < E)
    (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1) (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1)
    (hv : HumanMachine.Alone.value lam μ pg pb = lam * (Real.log (E + 1) - Real.binEntropy μ)) :
    μ * pg + (1 - μ) * (1 - pb) = E / (E + 1) := by
  have hE0 : 0 < E := by linarith
  have hEp : 0 < E + 1 := by linarith
  have hn : 0 < 1 - μ := by linarith
  obtain ⟨hp0, hp1⟩ := p_facts μ pg pb _ hμ0.le hμ1.le hpg0 hpg1 hpb0 hpb1 rfl
  set p := μ * pg + (1 - μ) * pb with hp
  obtain ⟨hY1, hY2⟩ := Y_pos E p hE1 hp0 hp1
  have hVF := value_le_F lam E μ pg pb p hlam hE0 hE hμ0.le hμ1.le hpg0 hpg1 hpb0 hpb1 hp
  have htanEq := tan_R2 lam E μ p hE1 hμ0 hμ1
  have hch := chain_eq lam E μ p (μ * (E + 1)) ((1 - μ) * (E + 1)) _ _ hlam hμ0.le hμ1.le
    (by positivity) (by positivity) hY1 hY2 hVF htanEq.le hv
  have hY1' : 1 - p + p * E = μ * (E + 1) := hch.1 hμ0
  have hY2' : p + (1 - p) * E = (1 - μ) * (E + 1) := by nlinarith
  have hpp0 : 0 < p := by nlinarith
  have hpp1 : p < 1 := by nlinarith
  have hFle := F_tan lam E μ p (μ * (E + 1)) ((1 - μ) * (E + 1)) hlam hμ0.le hμ1.le
    (by positivity) (by positivity) hY1 hY2
  rw [htanEq] at hFle
  -- Gibbs decomposition
  have e := value_eq lam μ pg pb p hp
  have g1 := gibbs_id lam E pg p hlam hE0 hE hpp0 hpp1
  have g2 := gibbs_id lam E (1 - pb) (1 - p) hlam hE0 hE (by linarith) (by linarith)
  rw [klt_symm] at g2
  have e2 : 1 - (1 - p) = p := by ring
  rw [e2] at g2
  obtain ⟨r1a, r1b⟩ := gibbs_r_mem E p hE0 hpp0 hpp1
  obtain ⟨r2a, r2b⟩ := gibbs_r_mem E (1 - p) hE0 (by linarith) (by linarith)
  rw [e2] at r2a r2b
  have k1 := klt_nonneg pg _ hpg0 hpg1 r1a r1b
  have k2 := klt_nonneg (1 - pb) _ (by linarith) (by linarith) r2a r2b
  rw [g1, g2] at e
  rw [hv] at e
  have hk : μ * klt pg (p * E / (1 - p + p * E))
      + (1 - μ) * klt (1 - pb) ((1 - p) * E / (p + (1 - p) * E)) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_pos hlam hcon
    nlinarith
  have m1 := mul_nonneg hμ0.le k1
  have m2 := mul_nonneg hn.le k2
  have hk1 : klt pg (p * E / (1 - p + p * E)) = 0 := by
    have : μ * klt pg (p * E / (1 - p + p * E)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hμ0.ne'
    · exact h
  have hk2 : klt (1 - pb) ((1 - p) * E / (p + (1 - p) * E)) = 0 := by
    have : (1 - μ) * klt (1 - pb) ((1 - p) * E / (p + (1 - p) * E)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hn.ne'
    · exact h
  have hpgE := klt_eq_zero pg _ hpg0 hpg1 r1a r1b hk1
  have hpbE := klt_eq_zero (1 - pb) _ (by linarith) (by linarith) r2a r2b hk2
  rw [hY1'] at hpgE
  rw [hY2'] at hpbE
  have hμn : (1 - μ) ≠ 0 := hn.ne'
  have hpb' : pb = 1 - (1 - p) * E / ((1 - μ) * (E + 1)) := by linarith
  rw [hpgE, hpb']
  field_simp
  ring

lemma reg2_attain (lam E μ : ℝ) (hlam : 0 < lam) (hE1 : 1 < E)
    (hE : Real.log E = 1 / lam) (hμ0' : 0 < μ) (hμ1' : μ < 1)
    (h1 : 1 < μ * (E + 1)) (h2 : μ * (E + 1) < E) :
    ∃ pg ∈ Set.Icc (0 : ℝ) 1, ∃ pb ∈ Set.Icc (0 : ℝ) 1,
      HumanMachine.Alone.value lam μ pg pb = lam * (Real.log (E + 1) - Real.binEntropy μ) := by
  have hE0 : 0 < E := by linarith
  have hEp : 0 < E + 1 := by linarith
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
  exact ⟨pg, ⟨hr0.le, hr1.le⟩, 1 - s, ⟨by linarith, by linarith⟩, hval⟩

lemma regime_pack (lam : ℝ) (hlam : 0 < lam) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ T A0 : ℝ,
      (∀ qg ∈ Set.Icc (0 : ℝ) 1, ∀ qb ∈ Set.Icc (0 : ℝ) 1,
        HumanMachine.Alone.value lam μ qg qb ≤ T) ∧
      (∃ pg0 ∈ Set.Icc (0 : ℝ) 1, ∃ pb0 ∈ Set.Icc (0 : ℝ) 1,
        HumanMachine.Alone.value lam μ pg0 pb0 = T) ∧
      (∀ qg ∈ Set.Icc (0 : ℝ) 1, ∀ qb ∈ Set.Icc (0 : ℝ) 1,
        HumanMachine.Alone.value lam μ qg qb = T → μ * qg + (1 - μ) * (1 - qb) = A0) ∧
      A0 = max (1 - μ) (max μ (Real.exp (1 / lam) / (Real.exp (1 / lam) + 1))) := by
  obtain ⟨hμ0, hμ1⟩ := hμ
  set E := Real.exp (1 / lam) with hEdef
  have hE1 : 1 < E := by
    rw [hEdef]; calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < _ := Real.exp_lt_exp.mpr (by positivity)
  have hE0 : 0 < E := by linarith
  have hEp : 0 < E + 1 := by linarith
  have hE : Real.log E = 1 / lam := Real.log_exp _
  rcases le_or_gt (μ * (E + 1)) 1 with hA | hA
  · -- regime 1
    refine ⟨1 - μ, 1 - μ, ?_, ⟨0, by simp, 0, by simp, ?_⟩, ?_, ?_⟩
    · intro qg hqg qb hqb
      exact ub_R1 lam E μ qg qb hlam hE1 hE hμ0 hμ1 hA hqg.1 hqg.2 hqb.1 hqb.2
    · simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
        HumanMachine.Alone.choiceProb]
    · intro qg hqg qb hqb hv
      exact reg1_eq lam E μ qg qb hlam hE1 hE hμ0 hμ1 hA hqg.1 hqg.2 hqb.1 hqb.2 hv
    · have h1 : μ ≤ 1 - μ := by nlinarith
      have h2 : E / (E + 1) ≤ 1 - μ := by
        rw [div_le_iff₀ hEp]; nlinarith
      rw [max_eq_left (max_le h1 h2)]
  rcases le_or_gt E (μ * (E + 1)) with hB | hB
  · -- regime 3
    refine ⟨μ, μ, ?_, ⟨1, by simp, 1, by simp, ?_⟩, ?_, ?_⟩
    · intro qg hqg qb hqb
      exact ub_R3 lam E μ qg qb hlam hE1 hE hμ0 hμ1 hB hqg.1 hqg.2 hqb.1 hqb.2
    · simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
        HumanMachine.Alone.choiceProb]
    · intro qg hqg qb hqb hv
      exact reg3_eq lam E μ qg qb hlam hE1 hE hμ0 hμ1 hB hqg.1 hqg.2 hqb.1 hqb.2 hv
    · have h2 : E / (E + 1) ≤ μ := by
        rw [div_le_iff₀ hEp]; linarith
      have h1 : 1 - μ ≤ μ := by
        have : 1 / 2 ≤ E / (E + 1) := by
          rw [div_le_div_iff₀ (by norm_num) hEp]; linarith
        linarith
      rw [max_eq_left h2, max_eq_right h1]
  · -- regime 2
    have hμ0' : 0 < μ := by
      by_contra hcon
      have : μ = 0 := le_antisymm (not_lt.mp hcon) hμ0
      rw [this] at hA; linarith
    have hμ1' : μ < 1 := by nlinarith
    obtain ⟨pg0, hg, pb0, hb, hval⟩ := reg2_attain lam E μ hlam hE1 hE hμ0' hμ1' hA hB
    refine ⟨lam * (Real.log (E + 1) - Real.binEntropy μ), E / (E + 1), ?_,
      ⟨pg0, hg, pb0, hb, hval⟩, ?_, ?_⟩
    · intro qg hqg qb hqb
      exact ub_R2 lam E μ qg qb hlam hE1 hE hμ0' hμ1' hqg.1 hqg.2 hqb.1 hqb.2
    · intro qg hqg qb hqb hv
      exact reg2_eq lam E μ qg qb hlam hE1 hE hμ0' hμ1' hA hB hqg.1 hqg.2 hqb.1 hqb.2 hv
    · have h1 : 1 - μ ≤ E / (E + 1) := by
        rw [le_div_iff₀ hEp]; nlinarith
      have h2 : μ ≤ E / (E + 1) := by
        rw [le_div_iff₀ hEp]; linarith
      rw [max_eq_right h2, max_eq_right h1]

lemma hma_value_zero (lam pg pb : ℝ) :
    HumanMachine.Alone.value lam 0 pg pb = 1 - pb := by
  simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
    HumanMachine.Alone.choiceProb]

lemma hma_optPair_zero (lam : ℝ) : (optPair lam 0).2 = 0 := by
  have hex : ∃ q : ℝ × ℝ, HumanMachine.Alone.IsOptimal lam 0 q.1 q.2 := by
    refine ⟨(0, 0), ?_⟩
    refine ⟨by simp, by simp, ?_⟩
    intro qg hqg qb hqb
    rw [hma_value_zero, hma_value_zero]
    linarith [hqb.1]
  have h : HumanMachine.Alone.IsOptimal lam 0 (optPair lam 0).1 (optPair lam 0).2 :=
    Classical.epsilon_spec hex
  obtain ⟨_, hb, hopt⟩ := h
  have := hopt 0 (by simp) 0 (by simp)
  rw [hma_value_zero, hma_value_zero] at this
  linarith [hb.1]

lemma hma_AStar_zero (lam : ℝ) : AStar lam 0 = 1 := by
  have h := hma_optPair_zero lam
  simp [AStar, HumanMachine.Alone.accuracy, h]

lemma hma_VStar_zero (lam : ℝ) : VStar lam 0 = 1 := by
  have h := hma_optPair_zero lam
  unfold VStar; rw [hma_value_zero, h]; norm_num

lemma opt_facts_pos (lam : ℝ) (hlam : 0 < lam) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    HumanMachine.Alone.IsOptimal lam μ (optPair lam μ).1 (optPair lam μ).2 ∧
      AStar lam μ = max (1 - μ) (max μ (Real.exp (1 / lam) / (Real.exp (1 / lam) + 1))) := by
  obtain ⟨T, A0, hub, ⟨pg0, hg, pb0, hb, hval⟩, hacc, hA0⟩ := regime_pack lam hlam μ hμ
  have hex : ∃ q : ℝ × ℝ, HumanMachine.Alone.IsOptimal lam μ q.1 q.2 :=
    ⟨(pg0, pb0), hg, hb, fun qg hqg qb hqb => by
      have := hub qg hqg qb hqb
      show HumanMachine.Alone.value lam μ qg qb ≤ HumanMachine.Alone.value lam μ pg0 pb0
      rw [hval]; exact this⟩
  have h : HumanMachine.Alone.IsOptimal lam μ (optPair lam μ).1 (optPair lam μ).2 :=
    Classical.epsilon_spec hex
  refine ⟨h, ?_⟩
  obtain ⟨h1, h2, hopt⟩ := h
  have hv : HumanMachine.Alone.value lam μ (optPair lam μ).1 (optPair lam μ).2 = T := by
    apply le_antisymm (hub _ h1 _ h2)
    have := hopt pg0 hg pb0 hb
    linarith
  have := hacc _ h1 _ h2 hv
  rw [← hA0, ← this]
  rfl

lemma opt_facts_zero (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    HumanMachine.Alone.IsOptimal 0 μ (optPair 0 μ).1 (optPair 0 μ).2 ∧ AStar 0 μ = 1 := by
  obtain ⟨hμ0, hμ1⟩ := hμ
  have hv : ∀ pg pb : ℝ, HumanMachine.Alone.value 0 μ pg pb = μ * pg + (1 - μ) * (1 - pb) := by
    intro pg pb
    simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost]
  have hle : ∀ pg ∈ Set.Icc (0 : ℝ) 1, ∀ pb ∈ Set.Icc (0 : ℝ) 1,
      μ * pg + (1 - μ) * (1 - pb) ≤ 1 := by
    intro pg hpg pb hpb
    have := mul_le_mul_of_nonneg_left hpg.2 hμ0
    have := mul_le_mul_of_nonneg_left (by linarith [hpb.1] : 1 - pb ≤ 1) (sub_nonneg.mpr hμ1)
    nlinarith
  have hex : ∃ q : ℝ × ℝ, HumanMachine.Alone.IsOptimal 0 μ q.1 q.2 := by
    refine ⟨(1, 0), by simp, by simp, ?_⟩
    intro qg hqg qb hqb
    rw [hv, hv]
    have := hle qg hqg qb hqb
    simp only [mul_one, sub_zero]; linarith
  have h : HumanMachine.Alone.IsOptimal 0 μ (optPair 0 μ).1 (optPair 0 μ).2 :=
    Classical.epsilon_spec hex
  refine ⟨h, ?_⟩
  obtain ⟨h1, h2, hopt⟩ := h
  have h3 := hopt 1 (by simp) 0 (by simp)
  rw [hv, hv] at h3
  have h4 := hle _ h1 _ h2
  unfold AStar HumanMachine.Alone.accuracy
  simp only [mul_one, sub_zero] at h3
  linarith

lemma value_concave (lam w μp pg pb : ℝ) (hlam : 0 ≤ lam) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hμp0 : 0 ≤ μp) (hμp1 : μp ≤ 1) (hpg0 : 0 ≤ pg) (hpg1 : pg ≤ 1)
    (hpb0 : 0 ≤ pb) (hpb1 : pb ≤ 1) :
    HumanMachine.Alone.value lam (w * μp) pg pb ≤
      w * HumanMachine.Alone.value lam μp pg pb + (1 - w) * HumanMachine.Alone.value lam 0 pg pb := by
  have hx : μp * pg + (1 - μp) * pb ∈ Set.Icc (0 : ℝ) 1 := by
    have := mul_nonneg hμp0 hpg0
    have := mul_nonneg (sub_nonneg.mpr hμp1) hpb0
    constructor
    · linarith
    · nlinarith
  have hc := Real.strictConcave_binEntropy.concaveOn.2 hx (⟨hpb0, hpb1⟩ : pb ∈ Set.Icc (0 : ℝ) 1)
    hw0 (sub_nonneg.mpr hw1) (by ring)
  simp only [smul_eq_mul] at hc
  have e : w * (μp * pg + (1 - μp) * pb) + (1 - w) * pb
      = (w * μp) * pg + (1 - w * μp) * pb := by ring
  rw [e] at hc
  have hc' := mul_le_mul_of_nonneg_left hc hlam
  rw [hma_value_zero]
  simp only [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
    HumanMachine.Alone.choiceProb]
  nlinarith

lemma prop1_core (lam : ℝ) (hlam : 0 ≤ lam) (w μp : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hμp : μp ∈ Set.Icc (0 : ℝ) 1) :
    AStar lam (w * μp) ≤ w * AStar lam μp + (1 - w) * 1 ∧
      VStar lam (w * μp) ≤ w * VStar lam μp + (1 - w) * 1 := by
  obtain ⟨hμp0, hμp1⟩ := hμp
  have hμ : w * μp ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hw0 hμp0, by nlinarith⟩
  have hopt : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      HumanMachine.Alone.IsOptimal lam μ (optPair lam μ).1 (optPair lam μ).2 := by
    intro μ hμ
    rcases hlam.eq_or_lt with h | h
    · subst h; exact (opt_facts_zero μ hμ).1
    · exact (opt_facts_pos lam h μ hμ).1
  constructor
  · rcases hlam.eq_or_lt with h | h
    · subst h
      rw [(opt_facts_zero _ hμ).2, (opt_facts_zero _ ⟨hμp0, hμp1⟩).2]; nlinarith
    · rw [(opt_facts_pos lam h _ hμ).2, (opt_facts_pos lam h _ ⟨hμp0, hμp1⟩).2]
      set M := Real.exp (1 / lam) / (Real.exp (1 / lam) + 1) with hM
      have hM1 : M ≤ 1 := by
        rw [hM, div_le_one (by positivity)]; linarith
      have hMA := le_max_right μp M
      have hMB := le_max_left μp M
      have hA1 := le_max_left (1 - μp) (max μp M)
      have hA2 := le_max_right (1 - μp) (max μp M)
      apply max_le
      · nlinarith
      · apply max_le
        · nlinarith
        · nlinarith
  · obtain ⟨hc, _⟩ : HumanMachine.Alone.IsOptimal lam (w * μp) (optPair lam (w * μp)).1
        (optPair lam (w * μp)).2 ∧ True := ⟨hopt _ hμ, trivial⟩
    obtain ⟨hc1, hc2, hcopt⟩ := hc
    obtain ⟨_, _, hpopt⟩ := hopt μp ⟨hμp0, hμp1⟩
    have h1 := value_concave lam w μp _ _ hlam hw0 hw1 hμp0 hμp1 hc1.1 hc1.2 hc2.1 hc2.2
    have h2 := hpopt _ hc1 _ hc2
    have h3 := hma_value_zero lam (optPair lam (w * μp)).1 (optPair lam (w * μp)).2
    have h4 := hc2.1
    unfold VStar
    nlinarith

theorem solution (lam : ℝ) (hlam : 0 ≤ lam) (π : Bool → Bool → ℝ) (hπ : IsPrior π) :
    AStar lam (priorGood π) ≤ AStarM lam π ∧ VStar lam (priorGood π) ≤ VStarM lam π := by
  obtain ⟨hpos, hsum⟩ := hπ
  have h1 : posterior π false = 0 := by
    simp [posterior, jointGood, isGood, Fintype.sum_bool]
  have hP : priorGood π = π true true := by
    simp [priorGood, isGood, Fintype.sum_bool]
  have hpt : probOut π true = π true true + π true false := by
    simp [probOut, Fintype.sum_bool]
  have hpf : probOut π false = π false true + π false false := by
    simp [probOut, Fintype.sum_bool]
  have h2 : posterior π true = π true true / (π true true + π true false) := by
    simp [posterior, jointGood, probOut, isGood, Fintype.sum_bool]
  have ha := hpos true true
  have hb := hpos true false
  have hc := hpos false true
  have hd := hpos false false
  have hne : π true true + π true false ≠ 0 := by positivity
  have hr : priorGood π = probOut π true * posterior π true := by
    rw [hP, h2, hpt]; field_simp
  have hrf : probOut π false = 1 - probOut π true := by
    rw [hpf, hpt]; linarith
  have hw0 : 0 ≤ probOut π true := by rw [hpt]; linarith
  have hw1 : probOut π true ≤ 1 := by rw [hpt]; linarith
  have hμp : posterior π true ∈ Set.Icc (0 : ℝ) 1 := by
    rw [h2]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]; linarith
  have core := prop1_core lam hlam (probOut π true) (posterior π true) hw0 hw1 hμp
  rw [← hr] at core
  obtain ⟨cA, cV⟩ := core
  constructor
  · unfold AStarM; rw [h1, hma_AStar_zero, hrf]; linarith
  · unfold VStarM; rw [h1, hma_VStar_zero, hrf]; linarith
