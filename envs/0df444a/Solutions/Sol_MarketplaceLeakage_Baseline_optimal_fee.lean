-- Prove2me | solution 1 for MarketplaceLeakage.Baseline.optimal_fee
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:55:47.549254+00:00
-- url     : https://prove2.me/submissions/dfc6c3f4-2812-4748-b8f6-6e9944f920a0

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

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

lemma revenue_formula {v c μ f pd : ℝ} (hμ : 0 < μ) (hf : 0 ≤ f)
    (hpd : IsSOpt v c μ f pd) :
    MProfit v μ f pd = if 2*μ ≤ f then 0 else f*(1-f/(2*μ)) := by
  rw [(seller_iff v c μ hμ f hf pd).1 hpd]
  split_ifs with hfm
  · rw [MProfit, g_large hμ (by linarith : μ ≤ v-(v-μ))]
    ring
  · rw [MProfit, g_small hμ (by linarith : 0 ≤ v-(v-f/2))
      (by linarith : v-(v-f/2) ≤ μ)]
    ring

lemma revenue_nonpos {v μ f pd : ℝ} (hf : f ≤ 0) : MProfit v μ f pd ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg hf (sub_nonneg.mpr (g_bounds μ (v-pd)).2)

noncomputable def rev (μ f : ℝ) : ℝ := f*(1-f/(2*μ))

lemma rev_scaled {μ : ℝ} (hμ : 0 < μ) (f : ℝ) :
    2*μ*rev μ f = 2*μ*f-f^2 := by
  unfold rev
  field_simp
  <;> ring

lemma rev_pos {μ f : ℝ} (hμ : 0 < μ) (hf : 0 < f) (hfm : f ≤ μ) : 0 < rev μ f := by
  have hd : f/(2*μ) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  exact mul_pos hf (sub_pos.mpr hd)

lemma quadratic_peak {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (f : ℝ) (hfa : f ≤ a) :
    rev μ f ≤ rev μ (min μ a) ∧ (rev μ f = rev μ (min μ a) → f = min μ a) := by
  have hs := rev_scaled hμ f
  by_cases hma : μ ≤ a
  · rw [min_eq_left hma]
    have ht := rev_scaled hμ μ
    constructor
    · nlinarith [sq_nonneg (f-μ)]
    · intro he
      have hz : (f-μ)^2 = 0 := by nlinarith
      have := (sq_eq_zero_iff).1 hz
      linarith
  · rw [min_eq_right (le_of_not_ge hma)]
    have ht := rev_scaled hμ a
    have hgap : 0 < 2*μ-a-f := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hfa) hgap.le
    constructor
    · nlinarith
    · intro he
      by_contra hne
      have hp := mul_pos (sub_pos.mpr (lt_of_le_of_ne hfa hne)) hgap
      nlinarith

lemma fee_peak {v c μ : ℝ} (hvc : c < v) (hμ : 0 < μ) :
    let g := min μ (v-c)
    IsSOpt v c μ g (v-g/2) ∧
    ∀ f pd : ℝ, f ≤ v-c → IsSOpt v c μ f pd →
      MProfit v μ f pd ≤ MProfit v μ g (v-g/2) ∧
      (MProfit v μ f pd = MProfit v μ g (v-g/2) → f = g) := by
  dsimp
  let g := min μ (v-c)
  have hg : 0 < g := lt_min hμ (sub_pos.mpr hvc)
  have hgm : g ≤ μ := min_le_left _ _
  have hgt : g < 2*μ := by linarith
  have hopt := good_seller (v:=v) (c:=c) hμ hg.le hgt
  have hR : MProfit v μ g (v-g/2) = rev μ g := by
    rw [revenue_formula hμ hg.le hopt, if_neg (not_le.mpr hgt)]
    rfl
  have hrpos := rev_pos hμ hg hgm
  refine ⟨hopt, ?_⟩
  intro f pd hfa hpd
  change MProfit v μ f pd ≤ MProfit v μ g (v-g/2) ∧ _
  rw [hR]
  by_cases hf : f ≤ 0
  · have hn := revenue_nonpos (v:=v) (μ:=μ) (pd:=pd) hf
    exact ⟨by linarith, by intro he; linarith⟩
  · have hf' : 0 ≤ f := le_of_lt (lt_of_not_ge hf)
    rw [revenue_formula hμ hf' hpd]
    split_ifs with hfm
    · exact ⟨hrpos.le, by intro he; linarith⟩
    · exact quadratic_peak hμ (sub_pos.mpr hvc) f hfa

lemma eq_iff {v c μ f pd : ℝ} (hvc : c < v) (hμ : 0 < μ) :
    IsEq v c μ f pd ↔ f = min μ (v-c) ∧ IsSOpt v c μ f pd := by
  have hp := fee_peak hvc hμ
  constructor
  · intro h
    refine ⟨?_, h.2.1⟩
    apply (hp.2 f pd h.1 h.2.1).2
    exact le_antisymm (hp.2 f pd h.1 h.2.1).1
      (h.2.2 _ _ (min_le_right _ _) hp.1)
  · rintro ⟨rfl, hpd⟩
    refine ⟨min_le_right _ _, hpd, ?_⟩
    intro f' pd' hf' hpd'
    have huniq := (seller_iff v c μ hμ _ (le_of_lt (lt_min hμ (sub_pos.mpr hvc))) pd).1 hpd
    have hlt : min μ (v-c) < 2*μ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    rw [if_neg (not_le.mpr hlt)] at huniq
    rw [huniq]
    exact (hp.2 f' pd' hf' hpd').1

lemma eq_facts {v c μ f pd : ℝ} (hvc : c < v) (hμ : 0 < μ) (h : IsEq v c μ f pd) :
    f = min μ (v-c) ∧ 0 < f ∧ f ≤ μ ∧ pd = v-f/2 ∧
      MProfit v μ f pd = rev μ f ∧ leakage v μ pd = f/(2*μ) := by
  have he := (eq_iff hvc hμ).1 h
  have hf : 0 < f := he.1 ▸ lt_min hμ (sub_pos.mpr hvc)
  have hfm : f ≤ μ := he.1 ▸ min_le_left _ _
  have hlt : f < 2*μ := by linarith
  have hpd := (seller_iff v c μ hμ f hf.le pd).1 he.2
  rw [if_neg (not_le.mpr hlt)] at hpd
  refine ⟨he.1, hf, hfm, hpd, ?_, ?_⟩
  · rw [revenue_formula hμ hf.le he.2, if_neg (not_le.mpr hlt)]
    rfl
  · rw [hpd, leakage, g_small hμ (by linarith : 0 ≤ v-(v-f/2))
      (by linarith : v-(v-f/2) ≤ μ)]
    ring

lemma leak_min {v c μ f pd : ℝ} (hvc : c < v) (hμ : 0 < μ) (h : IsEq v c μ f pd) :
    leakage v μ pd = min (1/2) ((v-c)/(2*μ)) := by
  have he := eq_facts hvc hμ h
  rw [he.2.2.2.2.2, he.1]
  by_cases hma : μ ≤ v-c
  · rw [min_eq_left hma, min_eq_left]
    · field_simp
    · apply (le_div_iff₀ (by positivity : 0 < 2*μ)).2
      linarith
  · rw [min_eq_right (le_of_not_ge hma), min_eq_right]
    apply (div_le_iff₀ (by positivity : 0 < 2*μ)).2
    linarith

lemma eq_exists {v c μ : ℝ} (hvc : c < v) (hμ : 0 < μ) :
    ∃ f pd : ℝ, IsEq v c μ f pd := by
  exact ⟨min μ (v-c), v-min μ (v-c)/2, (eq_iff hvc hμ).2 ⟨rfl, (fee_peak hvc hμ).1⟩⟩

lemma eq_values {v c μ f pd : ℝ} (hvc : c < v) (hμ : 0 < μ) (h : IsEq v c μ f pd) :
    f = min μ (v-c) ∧ pd = v-min (μ/2) ((v-c)/2) ∧
    MProfit v μ f pd = (if μ ≤ v-c then μ/2 else (v-c)*(1-(v-c)/(2*μ))) ∧
    leakage v μ pd = 1/μ*(v-pd) ∧ 0 < leakage v μ pd ∧ leakage v μ pd < 1 := by
  have he := eq_facts hvc hμ h
  refine ⟨he.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he.2.2.2.1, he.1]
    by_cases hma : μ ≤ v-c
    · rw [min_eq_left hma, min_eq_left (by linarith : μ/2 ≤ (v-c)/2)]
    · rw [min_eq_right (le_of_not_ge hma), min_eq_right (by linarith : (v-c)/2 ≤ μ/2)]
  · rw [he.2.2.2.2.1, rev, he.1]
    split_ifs with hma
    · rw [min_eq_left hma]
      field_simp
      <;> ring
    · rw [min_eq_right (le_of_not_ge hma)]
  · rw [he.2.2.2.2.2, he.2.2.2.1]
    ring
  · rw [he.2.2.2.2.2]
    exact div_pos he.2.1 (by positivity)
  · rw [he.2.2.2.2.2]
    exact (div_lt_one (by positivity)).2 (by linarith [he.2.2.1])

lemma comparative {v c μ₁ μ₂ f₁ pd₁ f₂ pd₂ : ℝ}
    (hvc : c < v) (hm1 : 0 < μ₁) (h12 : μ₁ < μ₂)
    (h1 : IsEq v c μ₁ f₁ pd₁) (h2 : IsEq v c μ₂ f₂ pd₂) :
    f₁ ≤ f₂ ∧ pd₂ ≤ pd₁ ∧ leakage v μ₂ pd₂ ≤ leakage v μ₁ pd₁ ∧
    MProfit v μ₁ f₁ pd₁ < MProfit v μ₂ f₂ pd₂ := by
  have hm2 : 0 < μ₂ := hm1.trans h12
  have e1 := eq_facts hvc hm1 h1
  have e2 := eq_facts hvc hm2 h2
  have hfees : f₁ ≤ f₂ := by
    rw [e1.1, e2.1]
    exact min_le_min h12.le le_rfl
  refine ⟨hfees, ?_, ?_, ?_⟩
  · rw [e1.2.2.2.1, e2.2.2.2.1]
    linarith
  · rw [leak_min hvc hm1 h1, leak_min hvc hm2 h2]
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_left (sub_pos.mpr hvc).le (by positivity) (by linarith)
  · have hdiv : f₁/(2*μ₂) < f₁/(2*μ₁) :=
      div_lt_div_of_pos_left e1.2.1 (by positivity) (by linarith)
    have hstrict : rev μ₁ f₁ < rev μ₂ f₁ := by
      exact mul_lt_mul_of_pos_left (by linarith) e1.2.1
    have hlt : f₁ < 2*μ₂ := by linarith [e1.2.2.1]
    have hs := good_seller (v:=v) (c:=c) hm2 e1.2.1.le hlt
    have hbound := h2.2.2 f₁ (v-f₁/2) h1.1 hs
    rw [revenue_formula hm2 e1.2.1.le hs, if_neg (not_le.mpr hlt)] at hbound
    rw [e1.2.2.2.2.1]
    exact hstrict.trans_le hbound

end LeakBaseProof

theorem solution (v c μ : ℝ) (hvc : c < v) (hμ : 0 < μ) (f pd : ℝ) :
    IsEq v c μ f pd ↔ (f = min μ (v - c) ∧ IsSOpt v c μ f pd) := by
  exact LeakBaseProof.eq_iff hvc hμ
