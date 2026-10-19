-- Prove2me | solution 1 for MarketplaceLeakage.Parity.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T17:05:35.466858+00:00
-- url     : https://prove2.me/submissions/307cd932-6fe8-4ba7-be37-7d2619dfceac

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting
import Definitions.Def_MarketplaceLeakage_Parity_Setting

open MarketplaceLeakage.Baseline
set_option maxHeartbeats 1600000

namespace LeakBaseProof

lemma g_bounds (μ x : ℝ) : 0 ≤ G μ x ∧ G μ x ≤ 1 := by
  unfold G
  exact ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

lemma g_small {μ x : ℝ} (hμ : 0 < μ) (hx : 0 ≤ x) (hxμ : x ≤ μ) :
    G μ x = x / μ := by
  simp only [G, max_eq_left (div_nonneg hx hμ.le),
    min_eq_left ((div_le_one hμ).2 hxμ)]

lemma g_large {μ x : ℝ} (hμ : 0 < μ) (hx : μ ≤ x) : G μ x = 1 := by
  have h : 1 ≤ x / μ := (le_div_iff₀ hμ).2 (by simpa using hx)
  exact min_eq_right (h.trans (le_max_left _ _))

lemma seller_small {v c μ f p : ℝ} (hμ : 0 < μ) (hp : p ≤ v) (hx : v - p ≤ μ) :
    μ * sProfit v c μ f p = μ * (v - c - f) + (f - (v-p)) * (v-p) := by
  rw [sProfit, g_small hμ (sub_nonneg.mpr hp) hx]
  field_simp
  <;> ring

lemma seller_large {v c μ f p : ℝ} (hμ : 0 < μ) (hx : μ ≤ v - p) :
    sProfit v c μ f p = p - c := by
  simp [sProfit, g_large hμ hx]

lemma seller_peak {v c μ f : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f) :
    let pstar := if 2 * μ ≤ f then v - μ else v - f / 2
    pstar ≤ v ∧ ∀ p : ℝ, p ≤ v →
      sProfit v c μ f p ≤ sProfit v c μ f pstar ∧
      (sProfit v c μ f p = sProfit v c μ f pstar → p = pstar) := by
  dsimp
  split_ifs with hfμ
  · refine ⟨by linarith, ?_⟩
    intro p hp
    rw [seller_large hμ (by linarith : μ ≤ v - (v-μ))]
    by_cases hx : μ ≤ v-p
    · rw [seller_large hμ hx]
      exact ⟨by linarith, by intro h; linarith⟩
    · have hxp : 0 < μ - (v-p) := by linarith
      have hfp : 0 < f - μ - (v-p) := by linarith
      have hm := mul_pos hxp hfp
      have hs := seller_small (v:=v) (c:=c) (f:=f) hμ hp (by linarith : v-p ≤ μ)
      have hstrict : sProfit v c μ f p < v - μ - c := by
        nlinarith
      exact ⟨hstrict.le, by intro he; linarith⟩
  · have hfμ' : f < 2 * μ := by linarith
    refine ⟨by linarith, ?_⟩
    intro p hp
    have hstar := seller_small (v:=v) (c:=c) (f:=f) (p:=v-f/2) hμ
      (by linarith) (by linarith)
    by_cases hx : v-p ≤ μ
    · have hs := seller_small (v:=v) (c:=c) (f:=f) hμ hp hx
      have hsq := sq_nonneg (v-p-f/2)
      constructor
      · nlinarith
      · intro he
        have hz : (v-p-f/2)^2 = 0 := by nlinarith
        have : v-p-f/2 = 0 := (sq_eq_zero_iff).1 hz
        linarith
    · rw [seller_large hμ (by linarith : μ ≤ v-p)]
      have hsq : 0 < (2*μ-f)^2 := sq_pos_of_pos (by linarith)
      have hstrict : p-c < sProfit v c μ f (v-f/2) := by nlinarith
      exact ⟨hstrict.le, by intro he; linarith⟩

lemma seller_iff (v c μ : ℝ) (hμ : 0 < μ) (f : ℝ) (hf : 0 ≤ f) (pd : ℝ) :
    IsSOpt v c μ f pd ↔ pd = (if 2 * μ ≤ f then v - μ else v - f / 2) := by
  have hp := seller_peak (v:=v) (c:=c) hμ hf
  constructor
  · intro h
    apply (hp.2 pd h.1).2
    exact le_antisymm (hp.2 pd h.1).1 (h.2 _ hp.1)
  · intro h
    subst pd
    exact ⟨hp.1, fun p hp' => (hp.2 p hp').1⟩

lemma good_seller {v c μ f : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f) (hfm : f < 2*μ) :
    IsSOpt v c μ f (v-f/2) := by
  apply (seller_iff v c μ hμ f hf _).2
  rw [if_neg (not_le.mpr hfm)]


end LeakBaseProof

open MarketplaceLeakage.Parity
namespace LeakParityProof
open LeakBaseProof

lemma delist_seller (v c μ pd : ℝ) :
    delistPayoff v c μ pd = sProfit v c μ (v-c) pd := by
  unfold delistPayoff sProfit
  ring

lemma delist_greatest {v c μ pd D : ℝ} (hopt : IsSOpt v c μ (v-c) pd)
    (hpc : c ≤ pd) (hD : delistPayoff v c μ pd = D) :
    IsGreatest ((fun p => delistPayoff v c μ p) '' Set.Icc c v) D := by
  refine ⟨⟨pd, ⟨hpc, hopt.1⟩, hD⟩, ?_⟩
  rintro y ⟨p, hp, rfl⟩
  dsimp only
  rw [← hD, delist_seller, delist_seller]
  exact hopt.2 p hp.2

lemma delist_closed {v c μ : ℝ} (hvc : c < v) (hμ : 0 < μ) :
    IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v)
      (if (v-c)/2 ≤ μ then (v-c)^2/(4*μ) else v-c-μ) := by
  have ha : 0 < v-c := sub_pos.mpr hvc
  split_ifs with ham
  · apply delist_greatest (pd:=v-(v-c)/2)
    · apply (seller_iff v c μ hμ (v-c) ha.le _).2
      split_ifs with hma <;> linarith
    · linarith
    · rw [delistPayoff, g_small hμ (by linarith : 0 ≤ v-(v-(v-c)/2))
        (by linarith : v-(v-(v-c)/2) ≤ μ)]
      ring
  · apply delist_greatest (pd:=v-μ)
    · apply (seller_iff v c μ hμ (v-c) ha.le _).2
      rw [if_pos (by linarith : 2*μ ≤ v-c)]
    · linarith
    · rw [delistPayoff, g_large hμ (by linarith : μ ≤ v-(v-μ))]
      ring

lemma delist_bounds {v c μ D : ℝ} (hvc : c < v)
    (hD : IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v) D) :
    0 ≤ D ∧ D ≤ v-c := by
  rcases hD.1 with ⟨pd, hp, rfl⟩
  have hg := g_bounds μ (v-pd)
  have hpc : 0 ≤ pd-c := sub_nonneg.mpr hp.1
  refine ⟨mul_nonneg hpc hg.1, ?_⟩
  change (pd-c)*G μ (v-pd) ≤ v-c
  calc
    _ ≤ (pd-c)*1 := mul_le_mul_of_nonneg_left hg.2 hpc
    _ ≤ v-c := by linarith [hp.2]

lemma accepts_iff {v c μ D : ℝ}
    (hD : IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v) D) (f : ℝ) :
    AcceptsB v c μ f ↔ f ≤ v-c-D := by
  constructor
  · intro h
    rcases hD.1 with ⟨pd, hp, he⟩
    dsimp only at he
    have hb := h pd hp.1 hp.2
    rw [he] at hb
    linarith
  · intro hf pd hpc hpv
    have hb := hD.2 ⟨pd, ⟨hpc, hpv⟩, rfl⟩
    linarith

lemma ppc_formula {v c μ q D : ℝ} (hvc : c < v)
    (hD : IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v) D) (f : ℝ) :
    ppcRev v c μ q f = if f ≤ v-c-D then f else if f ≤ v-c then (1-q)*f else 0 := by
  classical
  have hd := delist_bounds hvc hD
  have hn : AcceptsN v c f ↔ f ≤ v-c := by unfold AcceptsN; exact sub_nonneg
  simp only [ppcRev, accepts_iff hD, hn]
  split_ifs <;> try ring <;> linarith [hd.1]

lemma ppc_peak {v c μ q D : ℝ} (hvc : c < v) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hD : IsGreatest ((fun pd => delistPayoff v c μ pd) '' Set.Icc c v) D) :
    IsPPCValue v c μ q (max (v-c-D) ((1-q)*(v-c))) := by
  have hd := delist_bounds hvc hD
  have ha : 0 ≤ v-c := (sub_pos.mpr hvc).le
  have hB : (1-q)*(v-c) ≤ v-c := by nlinarith
  constructor
  · by_cases h : (1-q)*(v-c) ≤ v-c-D
    · refine ⟨v-c-D, ?_⟩
      rw [ppc_formula hvc hD, if_pos le_rfl, max_eq_left h]
    · refine ⟨v-c, ?_⟩
      rw [ppc_formula hvc hD, if_neg (by linarith : ¬ v-c ≤ v-c-D),
        if_pos le_rfl, max_eq_right (by linarith)]
  · rintro y ⟨f, rfl⟩
    rw [ppc_formula hvc hD]
    split_ifs with hft hfa
    · exact hft.trans (le_max_left _ _)
    · exact (mul_le_mul_of_nonneg_left hfa (by linarith)).trans (le_max_right _ _)
    · exact (sub_nonneg.mpr hd.2).trans (le_max_left _ _)

noncomputable def r (μ q f : ℝ) := f*(1-q*min (f/(2*μ)) 1)

lemma no_formula {v c μ q f pd : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f)
    (hpd : IsSOpt v c μ f pd) : noRev v μ q f pd = r μ q f := by
  rw [noRev, (seller_iff v c μ hμ f hf pd).1 hpd]
  split_ifs with hfm
  · rw [g_large hμ (by linarith : μ ≤ v-(v-μ)), r,
      min_eq_right ((le_div_iff₀ (by positivity : 0 < 2*μ)).2 (by linarith))]
  · rw [g_small hμ (by linarith : 0 ≤ v-(v-f/2)) (by linarith : v-(v-f/2) ≤ μ),
      r, min_eq_left ((div_le_one (by positivity : 0 < 2*μ)).2 (by linarith))]
    ring

lemma no_nonpos {v μ q f pd : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hf : f ≤ 0) :
    noRev v μ q f pd ≤ 0 := by
  have hg := g_bounds μ (v-pd)
  have hprod : q*G μ (v-pd) ≤ 1 := by nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg hf (by linarith)

lemma r_nonneg {μ q f : ℝ} (hμ : 0 < μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hf : 0 ≤ f) :
    0 ≤ r μ q f := by
  have hmin : 0 ≤ min (f/(2*μ)) 1 := le_min (div_nonneg hf (by positivity)) (by norm_num)
  have hmax : min (f/(2*μ)) 1 ≤ 1 := min_le_right _ _
  have hprod : q*min (f/(2*μ)) 1 ≤ 1 := by nlinarith
  exact mul_nonneg hf (by linarith)

lemma realizes {v c μ q f : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f) :
    ∃ pd, IsSOpt v c μ f pd ∧ noRev v μ q f pd = r μ q f := by
  let pd := if 2*μ ≤ f then v-μ else v-f/2
  have hs : IsSOpt v c μ f pd := (seller_iff v c μ hμ f hf pd).2 rfl
  exact ⟨pd, hs, no_formula hμ hf hs⟩

lemma no_exists {v c μ q : ℝ} (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ W, IsNoPPCValue v c μ q W := by
  have ha : 0 ≤ v-c := (sub_pos.mpr hvc).le
  have hc : Continuous (r μ q) := by unfold r; fun_prop
  obtain ⟨f, hf, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0:ℝ) (v-c)).Nonempty from ⟨0, le_rfl, ha⟩) hc.continuousOn
  obtain ⟨pd, hs, he⟩ := realizes (v:=v) (c:=c) (q:=q) hμ hf.1
  refine ⟨r μ q f, ⟨⟨f, pd, hf.2, hs, he.symm⟩, ?_⟩⟩
  rintro w ⟨g, p, hga, hsp, rfl⟩
  by_cases hg : 0 ≤ g
  · rw [no_formula hμ hg hsp]
    exact hmax ⟨hg, hga⟩
  · exact (no_nonpos hq0 hq1 (le_of_not_ge hg)).trans (r_nonneg hμ hq0 hq1 hf.1)

lemma r_small {μ q f : ℝ} (hμ : 0 < μ) (hf : f ≤ 2*μ) :
    r μ q f = f*(1-q*f/(2*μ)) := by
  rw [r, min_eq_left ((div_le_one (by positivity : 0 < 2*μ)).2 hf)]
  ring

lemma r_large {μ q f : ℝ} (hμ : 0 < μ) (hf : 2*μ ≤ f) :
    r μ q f = (1-q)*f := by
  rw [r, min_eq_right ((le_div_iff₀ (by positivity : 0 < 2*μ)).2 (by simpa using hf))]
  ring

lemma r_scaled {μ q f : ℝ} (hμ : 0 < μ) (hf : f ≤ 2*μ) :
    2*μ*r μ q f = 2*μ*f-q*f^2 := by
  rw [r_small hμ hf]
  field_simp
  <;> ring

lemma r_mono_lowq {μ q f a : ℝ} (hμ : 0 < μ) (hq : q ≤ 1/2)
    (hf : 0 ≤ f) (hfa : f ≤ a) : r μ q f ≤ r μ q a := by
  have quad : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 2*μ → r μ q x ≤ r μ q y := by
    intro x y hx hxy hym
    have hsx := r_scaled (q:=q) hμ (hxy.trans hym)
    have hsy := r_scaled (q:=q) hμ hym
    have hfac : 0 ≤ 2*μ-q*(x+y) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2-q) (by linarith : 0 ≤ x+y)]
    have hp := mul_nonneg (sub_nonneg.mpr hxy) hfac
    nlinarith
  by_cases hfm : f ≤ 2*μ
  · by_cases ham : a ≤ 2*μ
    · exact quad f a hf hfa ham
    · have hmid := quad f (2*μ) hf hfm le_rfl
      have htail : r μ q (2*μ) ≤ r μ q a := by
        rw [r_large hμ le_rfl, r_large hμ (le_of_not_ge ham)]
        exact mul_le_mul_of_nonneg_left (le_of_not_ge ham) (by linarith)
      exact hmid.trans htail
  · rw [r_large hμ (le_of_not_ge hfm), r_large hμ ((le_of_not_ge hfm).trans hfa)]
    exact mul_le_mul_of_nonneg_left hfa (by linarith)

lemma no_lowq {v c μ q : ℝ} (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q) (hq : q < 1/2) :
    IsNoPPCValue v c μ q (r μ q (v-c)) := by
  have ha : 0 ≤ v-c := (sub_pos.mpr hvc).le
  obtain ⟨pd, hs, he⟩ := realizes (v:=v) (c:=c) (q:=q) hμ ha
  refine ⟨⟨v-c, pd, le_rfl, hs, he.symm⟩, ?_⟩
  rintro w ⟨f, p, hfa, hsp, rfl⟩
  by_cases hf : 0 ≤ f
  · rw [no_formula hμ hf hsp]
    exact r_mono_lowq hμ hq.le hf hfa
  · exact (no_nonpos hq0.le (by linarith) (le_of_not_ge hf)).trans
      (r_nonneg hμ hq0.le (by linarith) ha)

noncomputable def d (μ a : ℝ) := if a/2 ≤ μ then a^2/(4*μ) else a-μ
noncomputable def pv (μ q a : ℝ) := max (a-d μ a) ((1-q)*a)

lemma pv_nonneg {μ q a : ℝ} (ha : 0 ≤ a) (hq : q ≤ 1) : 0 ≤ pv μ q a := by
  exact (mul_nonneg (sub_nonneg.mpr hq) ha).trans (le_max_right _ _)

lemma r_bound {μ q a f : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hf : 0 ≤ f) (hfa : f ≤ a) (hnot : ¬ (q < 1/2 ∧ a/2 < μ)) :
    r μ q f ≤ pv μ q a := by
  by_cases hql : q < 1/2
  · have ham : 2*μ ≤ a := by by_contra h; exact hnot ⟨hql, by linarith⟩
    calc
      r μ q f ≤ r μ q a := r_mono_lowq hμ hql.le hf hfa
      _ = (1-q)*a := r_large hμ ham
      _ ≤ pv μ q a := le_max_right _ _
  · have hqh : 1/2 ≤ q := le_of_not_gt hql
    by_cases ham : a/2 ≤ μ
    · have hs := r_scaled (q:=q) hμ (by linarith : f ≤ 2*μ)
      have ht : 4*μ*(a-a^2/(4*μ)) = 4*μ*a-a^2 := by field_simp <;> ring
      have h1 := mul_nonneg (sub_nonneg.mpr hfa) (by linarith : 0 ≤ 4*μ-a-f)
      have h2 := mul_nonneg (sub_nonneg.mpr hqh) (sq_nonneg f)
      have hb : r μ q f ≤ a-a^2/(4*μ) := by nlinarith
      exact hb.trans (by simpa only [pv, d, if_pos ham] using
        (le_max_left (a-a^2/(4*μ)) ((1-q)*a)))
    · have hthreshold : a-d μ a = μ := by rw [d, if_neg ham]; ring
      by_cases hfm : f ≤ 2*μ
      · have hs := r_scaled (q:=q) hμ hfm
        have h1 := sq_nonneg (f-2*μ)
        have h2 := mul_nonneg (sub_nonneg.mpr hqh) (sq_nonneg f)
        have hb : r μ q f ≤ μ := by nlinarith
        exact hb.trans (by simpa only [pv, hthreshold] using
          (le_max_left μ ((1-q)*a)))
      · rw [r_large hμ (le_of_not_ge hfm)]
        exact (mul_le_mul_of_nonneg_left hfa (sub_nonneg.mpr hq1)).trans (le_max_right _ _)

lemma r_strict {μ q a : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hq0 : 0 < q)
    (hq : q < 1/2) (ham : a/2 < μ) : pv μ q a < r μ q a := by
  rw [pv, d, if_pos ham.le]
  have hs := r_scaled (q:=q) hμ (by linarith : a ≤ 2*μ)
  have ht : 4*μ*(a-a^2/(4*μ)) = 4*μ*a-a^2 := by field_simp <;> ring
  apply max_lt_iff.mpr
  constructor
  · have hp := mul_pos (sub_pos.mpr hq) (sq_pos_of_pos ha)
    nlinarith
  · have hp := mul_pos hq0 (mul_pos ha (by linarith : 0 < 2*μ-a))
    nlinarith

lemma ppc_value {v c μ q : ℝ} (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    IsPPCValue v c μ q (pv μ q (v-c)) := by
  exact ppc_peak hvc hq0.le hq1 (delist_closed hvc hμ)

lemma comparison {v c μ q V W : ℝ} (hvc : c < v) (hμ : 0 < μ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (hV : IsPPCValue v c μ q V)
    (hW : IsNoPPCValue v c μ q W) :
    (V < W ↔ q < 1/2 ∧ (v-c)/2 < μ) ∧ (¬ (q < 1/2 ∧ (v-c)/2 < μ) → W ≤ V) := by
  have hv : V = pv μ q (v-c) := hV.unique (ppc_value hvc hμ hq0 hq1)
  have hb : ¬ (q < 1/2 ∧ (v-c)/2 < μ) → W ≤ V := by
    intro hn
    rcases hW.1 with ⟨f, pd, hfa, hs, he⟩
    rw [he, hv]
    by_cases hf : 0 ≤ f
    · rw [no_formula hμ hf hs]
      exact r_bound (sub_pos.mpr hvc) hμ hq0 hq1 hf hfa hn
    · exact (no_nonpos hq0.le hq1 (le_of_not_ge hf)).trans
        (pv_nonneg (sub_pos.mpr hvc).le hq1)
  refine ⟨⟨?_, ?_⟩, hb⟩
  · intro hlt
    by_contra hn
    exact (not_lt_of_ge (hb hn)) hlt
  · rintro ⟨hq, ham⟩
    have hw : W = r μ q (v-c) := hW.unique (no_lowq hvc hμ hq0 hq)
    rw [hv, hw]
    exact r_strict (sub_pos.mpr hvc) hμ hq0 hq ham

end LeakParityProof

theorem solution (v c μ q : ℝ) (hvc : c < v) (hμ : 0 < μ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∃ V, IsPPCValue v c μ q V) ∧ (∃ W, IsNoPPCValue v c μ q W) ∧
    ∀ V W, IsPPCValue v c μ q V → IsNoPPCValue v c μ q W →
      ((V < W ↔ (q < 1 / 2 ∧ (v - c) / 2 < μ)) ∧
       (¬ (q < 1 / 2 ∧ (v - c) / 2 < μ) → W ≤ V)) := by
  refine ⟨⟨_, LeakParityProof.ppc_value hvc hμ hq0 hq1⟩,
    LeakParityProof.no_exists hvc hμ hq0.le hq1, ?_⟩
  intro V W hV hW
  exact LeakParityProof.comparison hvc hμ hq0 hq1 hV hW
