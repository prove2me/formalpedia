-- Prove2me | solution 1 for MinEarnings.Static.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:56:55.4479+00:00
-- url     : https://prove2.me/submissions/7f51e589-ec20-47ce-b448-20b98cc0d9cb

import Mathlib
import Definitions.Def_MinEarnings_Static_Setting

set_option autoImplicit false
open MinEarnings.Threshold MinEarnings.Static

lemma mea_util_pos (D S : ℝ → ℝ) (hP : Primitives D S) {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z) :
    0 < util D S p z := by
  unfold util quantity
  exact div_pos (lt_min (hP.D_pos p hp) (hP.S_pos z hz)) (hP.S_pos z hz)

lemma mea_util_le_one (D S : ℝ → ℝ) (hP : Primitives D S) {p z : ℝ} (hz : 0 < z) :
    util D S p z ≤ 1 := by
  unfold util quantity
  rw [div_le_one (hP.S_pos z hz)]
  exact min_le_right _ _

lemma mea_static_of_floor (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S)
    (w z : ℕ → ℝ) (hfeas : IsFeasible w w) (heq : IsEquilibrium D S w w z) (t : ℕ)
    (hwt : M / util D S (w t) (z t) ≤ w t) : IsStaticallyStable D S M :=
  ⟨w t, w t, z t, util D S (w t) (z t), (hfeas t).2, (hfeas t).2, (heq t).1.le,
    mea_util_pos D S hP (hfeas t).2 (heq t).1, mea_util_le_one D S hP (heq t).1, rfl, (heq t).2,
    hwt, le_rfl⟩

lemma mea_static_of_inc (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : IsFeasible w w) (heq : IsEquilibrium D S w w z)
    (hrule : MinEarningsRule D S M w w z) (t : ℕ)
    (hinc : util D S (w t) (z t) ≤ util D S (w (t + 1)) (z (t + 1))) :
    IsStaticallyStable D S M := by
  refine mea_static_of_floor D S M hP w z hfeas heq (t + 1) ?_
  calc M / util D S (w (t + 1)) (z (t + 1)) ≤ M / util D S (w t) (z t) :=
        div_le_div_of_nonneg_left hM.le (mea_util_pos D S hP (hfeas t).2 (heq t).1) hinc
    _ ≤ w (t + 1) := hrule t

lemma mea_static_implies_stable (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (hM : 0 < M) :
    IsStaticallyStable D S M → IsStable D S M := by
  rintro ⟨p, w, z, u, hp, hw, hz, hu0, hu1, hu, hzw, hMu, hwp⟩
  have hwpos : 0 < w := lt_of_lt_of_le (div_pos hM hu0) hMu
  have hzpos : 0 < z := by rw [hzw]; exact mul_pos hwpos hu0
  refine ⟨fun _ => p, fun _ => w, fun _ => z, ?_, ?_, ?_, ⟨w, fun _ => le_rfl⟩, ?_⟩
  · exact fun _ => ⟨hp, hw⟩
  · exact fun _ => ⟨hzpos, by rw [← hu]; exact hzw⟩
  · intro t; show M / util D S p z ≤ w; rw [← hu]; exact hMu
  · refine Filter.Eventually.of_forall (fun t => ?_)
    show 0 ≤ (p - w) * quantity D S p z
    exact mul_nonneg (sub_nonneg.2 hwp) (le_min (hP.D_pos p hp).le (hP.S_pos z hzpos).le)

lemma mea_fixpt (D S : ℝ → ℝ) (hP : Primitives D S) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b ≤ a) (hc : 0 < c) (hceq : c = b * util D S a c) :
    ∃ x, c ≤ x ∧ x ≤ b ∧ x = b * util D S b x := by
  have hbpos : 0 < b := by
    rcases hb.eq_or_lt with h | h
    · rw [← h] at hceq; simp at hceq; linarith
    · exact h
  have hu1 := mea_util_le_one D S hP (p := a) hc
  have hcb : c ≤ b := by
    calc c = b * util D S a c := hceq
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left hu1 hb
      _ = b := mul_one b
  have hcont : ContinuousOn (fun x => x - b * util D S b x) (Set.Icc c b) := by
    have hSc : ∀ x ∈ Set.Icc c b, ContinuousAt S x := fun x hx =>
      hP.S_continuousOn.continuousAt (Ici_mem_nhds (lt_of_lt_of_le hc hx.1))
    refine continuousOn_id.sub (continuousOn_const.mul ?_)
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hc hx.1
    have h1 : ContinuousAt (fun x => quantity D S b x / S x) x := by
      unfold quantity
      exact (continuousAt_const.min (hSc x hx)).div (hSc x hx) (hP.S_pos x hxpos).ne'
    exact h1.continuousWithinAt
  have hDle : D a ≤ D b := hP.D_strictAntiOn.antitoneOn (Set.mem_Ici.2 hb) (Set.mem_Ici.2 ha) hab
  have hlo : c - b * util D S b c ≤ 0 := by
    have : util D S a c ≤ util D S b c := by
      unfold util quantity
      exact div_le_div_of_nonneg_right (min_le_min_right _ hDle) (hP.S_pos c hc).le
    nlinarith
  have hhi : 0 ≤ b - b * util D S b b := by
    have := mea_util_le_one D S hP (p := b) hbpos
    nlinarith
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hcb hcont ⟨hlo, hhi⟩
  exact ⟨x, hx.1, hx.2, by simp only at hx0; linarith⟩

lemma mea_reduce (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (hM : 0 < M) (h : IsStable D S M) :
    ∃ w z : ℕ → ℝ, IsFeasible w w ∧ IsEquilibrium D S w w z ∧ MinEarningsRule D S M w w z ∧
      ∃ B, ∀ t, w t ≤ B := by
  obtain ⟨p, w, z, hf, he, hr, ⟨B, hB⟩, hprof⟩ := h
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hprof
  have hpw : ∀ s, T ≤ s → w s ≤ p s := by
    intro s hs
    have h1 := hT s hs
    have hz := (he s).1
    have hQ : 0 < quantity D S (p s) (z s) :=
      lt_min (hP.D_pos _ (hf s).1) (hP.S_pos _ hz)
    by_contra hlt
    push_neg at hlt
    have : (p s - w s) * quantity D S (p s) (z s) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hQ
    exact absurd h1 (not_le.2 this)
  have hex : ∀ t, ∃ x, z (t + T) ≤ x ∧ x ≤ w (t + T) ∧ x = w (t + T) * util D S (w (t + T)) x := by
    intro t
    exact mea_fixpt D S hP (hf (t + T)).1 (hf (t + T)).2 (hpw (t + T) (by omega)) (he (t + T)).1
      (he (t + T)).2
  choose z' hz1 hz2 hz3 using hex
  refine ⟨fun t => w (t + T), z', fun t => ⟨(hf (t + T)).2, (hf (t + T)).2⟩, ?_, ?_, ⟨B, fun t => hB _⟩⟩
  · intro t
    exact ⟨lt_of_lt_of_le (he (t + T)).1 (hz1 t), hz3 t⟩
  · intro t
    have hr' := hr (t + T)
    have hup := mea_util_pos D S hP (hf (t + T)).1 (he (t + T)).1
    have hwpos : 0 < w (t + T) := by
      rcases (hf (t + T)).2.eq_or_lt with h | h
      · have := (he (t + T)).2; rw [← h] at this; simp at this; linarith [(he (t + T)).1]
      · exact h
    have hzp : 0 < z' t := lt_of_lt_of_le (he (t + T)).1 (hz1 t)
    have hu' : util D S (p (t + T)) (z (t + T)) ≤ util D S (w (t + T)) (z' t) := by
      have e1 := (he (t + T)).2
      have e2 := hz3 t
      have := hz1 t
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_lt_mul_of_pos_left hcon hwpos]
    show M / util D S (w (t + T)) (z' t) ≤ w (t + 1 + T)
    have hM' := div_le_div_of_nonneg_left hM.le hup hu'
    have hr2 := hr (t + T)
    rw [show t + T + 1 = t + 1 + T by omega] at hr2
    exact hM'.trans hr2

lemma mea_limit (D S : ℝ → ℝ) (M : ℝ) (hP : Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : IsFeasible w w) (heq : IsEquilibrium D S w w z)
    (hrule : MinEarningsRule D S M w w z) (hbdd : ∃ B, ∀ t, w t ≤ B)
    (hdec : ∀ t, util D S (w (t + 1)) (z (t + 1)) < util D S (w t) (z t))
    (hlow : ∀ t, w t < M / util D S (w t) (z t)) :
    ∃ wl ul : ℝ, Filter.Tendsto w Filter.atTop (nhds wl) ∧
      Filter.Tendsto (fun t => util D S (w t) (z t)) Filter.atTop (nhds ul) ∧
      0 < ul ∧ ul ≤ 1 ∧ M / ul ≤ wl ∧ ul = util D S wl (wl * ul) := by
  have hupos : ∀ t, 0 < util D S (w t) (z t) := fun t =>
    mea_util_pos D S hP (hfeas t).2 (heq t).1
  have hu1 : ∀ t, util D S (w t) (z t) ≤ 1 := fun t => mea_util_le_one D S hP (heq t).1
  have hwstep : ∀ t, w t ≤ w (t + 1) := fun t => by
    have h1 := hlow t
    have h2 := hrule t
    linarith
  have hwmono : Monotone w := monotone_nat_of_le_succ hwstep
  obtain ⟨B, hB⟩ := hbdd
  have hwlim : Filter.Tendsto w Filter.atTop (nhds (⨆ t, w t)) :=
    tendsto_atTop_ciSup hwmono ⟨B, by rintro _ ⟨t, rfl⟩; exact hB t⟩
  have humono : Antitone (fun t => util D S (w t) (z t)) :=
    antitone_nat_of_succ_le (fun t => (hdec t).le)
  have hulim : Filter.Tendsto (fun t => util D S (w t) (z t)) Filter.atTop
      (nhds (⨅ t, util D S (w t) (z t))) :=
    tendsto_atTop_ciInf humono ⟨0, by rintro _ ⟨t, rfl⟩; exact (hupos t).le⟩
  set wl : ℝ := ⨆ t, w t with hwl_def
  set ul : ℝ := ⨅ t, util D S (w t) (z t) with hul_def
  have hwl0 : 0 ≤ wl := ge_of_tendsto' hwlim (fun t => (hfeas t).2)
  have hprod : M ≤ wl * ul := by
    have hl : Filter.Tendsto (fun t => w (t + 1) * util D S (w t) (z t)) Filter.atTop
        (nhds (wl * ul)) :=
      (hwlim.comp (Filter.tendsto_add_atTop_nat 1)).mul hulim
    refine ge_of_tendsto' hl (fun t => ?_)
    have := hrule t
    rwa [div_le_iff₀ (hupos t)] at this
  have hul0 : 0 < ul := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hwl0 h]
  have hul1 : ul ≤ 1 := le_of_tendsto' hulim hu1
  have hwl : M / ul ≤ wl := by
    rw [div_le_iff₀ hul0]; linarith
  have hxpos : 0 < wl * ul := lt_of_lt_of_le hM hprod
  have hzlim : Filter.Tendsto z Filter.atTop (nhds (wl * ul)) := by
    have : z = fun t => w t * util D S (w t) (z t) := funext (fun t => (heq t).2)
    rw [this]
    exact hwlim.mul hulim
  have hDt : Filter.Tendsto (fun t => D (w t)) Filter.atTop (nhds (D wl)) := by
    have h1 : Filter.Tendsto D (nhdsWithin wl (Set.Ici 0)) (nhds (D wl)) :=
      (hP.D_continuousOn wl (Set.mem_Ici.2 hwl0)).tendsto
    exact h1.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hwlim
      (Filter.Eventually.of_forall (fun t => Set.mem_Ici.2 (hfeas t).2)))
  have hSc : ContinuousAt S (wl * ul) :=
    hP.S_continuousOn.continuousAt (Ici_mem_nhds hxpos)
  have hSt : Filter.Tendsto (fun t => S (z t)) Filter.atTop (nhds (S (wl * ul))) :=
    hSc.tendsto.comp hzlim
  have hlim2 : Filter.Tendsto (fun t => util D S (w t) (z t)) Filter.atTop
      (nhds (util D S wl (wl * ul))) := by
    unfold util quantity
    exact (hDt.min hSt).div hSt (hP.S_pos _ hxpos).ne'
  exact ⟨wl, ul, hwlim, hulim, hul0, hul1, hwl, tendsto_nhds_unique hulim hlim2⟩

theorem solution (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M) :
    MinEarnings.Threshold.IsStable D S M ↔ IsStaticallyStable D S M := by
  refine ⟨fun h => ?_, mea_static_implies_stable D S M hP hM⟩
  obtain ⟨w, z, hfeas, heq, hrule, hbdd⟩ := mea_reduce D S M hP hM h
  by_cases c1 : ∃ t, util D S (w t) (z t) ≤ util D S (w (t + 1)) (z (t + 1))
  · obtain ⟨t, ht⟩ := c1
    exact mea_static_of_inc D S M hP hM w z hfeas heq hrule t ht
  by_cases c2 : ∃ t, M / util D S (w t) (z t) ≤ w t
  · obtain ⟨t, ht⟩ := c2
    exact mea_static_of_floor D S M hP w z hfeas heq t ht
  push_neg at c1 c2
  obtain ⟨wl, ul, hwl, hul, hu0, hu1, hMu, hfix⟩ :=
    mea_limit D S M hP hM w z hfeas heq hrule hbdd (fun t => c1 t) (fun t => c2 t)
  have hwl0 : 0 ≤ wl := ge_of_tendsto' hwl (fun t => (hfeas t).2)
  exact ⟨wl, wl, wl * ul, ul, hwl0, hwl0, mul_nonneg hwl0 hu0.le, hu0, hu1, hfix, rfl, hMu, le_rfl⟩
