-- Prove2me | solution 1 for MinEarnings.Static.limit_is_static
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:56:56.478343+00:00
-- url     : https://prove2.me/submissions/0df83906-aa70-49ef-9236-62437f3779cd

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

theorem solution (D S : ℝ → ℝ) (M : ℝ) (hP : MinEarnings.Threshold.Primitives D S) (hM : 0 < M)
    (w z : ℕ → ℝ) (hfeas : MinEarnings.Threshold.IsFeasible w w) (heq : MinEarnings.Threshold.IsEquilibrium D S w w z)
    (hrule : MinEarnings.Threshold.MinEarningsRule D S M w w z) (hbdd : ∃ B, ∀ t, w t ≤ B)
    (hdec : ∀ t, MinEarnings.Threshold.util D S (w (t + 1)) (z (t + 1)) < MinEarnings.Threshold.util D S (w t) (z t))
    (hlow : ∀ t, w t < M / MinEarnings.Threshold.util D S (w t) (z t)) :
    ∃ wl ul : ℝ, Filter.Tendsto w Filter.atTop (nhds wl) ∧
      Filter.Tendsto (fun t => MinEarnings.Threshold.util D S (w t) (z t)) Filter.atTop (nhds ul) ∧
      0 < ul ∧ ul ≤ 1 ∧ M / ul ≤ wl ∧ ul = MinEarnings.Threshold.util D S wl (wl * ul) :=
  mea_limit D S M hP hM w z hfeas heq hrule hbdd hdec hlow
