-- Prove2me | solution 1 for LambdaVaRAmb.Robust.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:52:40.373483+00:00
-- url     : https://prove2.me/submissions/ddb5c15c-a2cf-4c80-8c2e-1a727f584f65

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting

open MeasureTheory Set LambdaVaRAmb.Robust
open scoped ENNReal

namespace LRobP5Main

variable {φ : ℝ → EReal}

lemma fin_eq (hφ : IsPhiFunction φ) {z : ℝ} (hz : 0 ≤ z) (h : φ z < ⊤) :
    φ z = ((φ z).toReal : EReal) :=
  (EReal.coe_toReal h.ne (hφ.ne_bot z hz)).symm

/-- convexity on the effective domain, as real numbers -/
lemma conv_real (hφ : IsPhiFunction φ) {s t θ : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (hfs : φ s < ⊤) (hft : φ t < ⊤) :
    φ (θ * s + (1 - θ) * t) < ⊤ ∧
      (φ (θ * s + (1 - θ) * t)).toReal ≤ θ * (φ s).toReal + (1 - θ) * (φ t).toReal := by
  have hc := hφ.convex s t θ hs ht h0 h1
  rw [fin_eq hφ hs hfs, fin_eq hφ ht hft] at hc
  have e : ((θ : EReal) * ((φ s).toReal : EReal) + ((1 - θ : ℝ) : EReal) * ((φ t).toReal : EReal))
      = ((θ * (φ s).toReal + (1 - θ) * (φ t).toReal : ℝ) : EReal) := by
    simp only [EReal.coe_add, EReal.coe_mul]
  rw [e] at hc
  have hlt : φ (θ * s + (1 - θ) * t) < ⊤ := lt_of_le_of_lt hc (EReal.coe_lt_top _)
  refine ⟨hlt, ?_⟩
  have hpos : 0 ≤ θ * s + (1 - θ) * t := by nlinarith
  rw [fin_eq hφ hpos hlt] at hc
  exact_mod_cast hc

/-- existence of a subgradient at a point with domain points on both sides -/
lemma subgrad (hφ : IsPhiFunction φ) {z0 m w0 : ℝ} (hz0 : 0 ≤ z0) (hzm : z0 < m) (hmw : m < w0)
    (hfz : φ z0 < ⊤) (hfw : φ w0 < ⊤) :
    φ m < ⊤ ∧ ∃ c : ℝ, ∀ z : ℝ, 0 ≤ z → (((φ m).toReal + c * (z - m) : ℝ) : EReal) ≤ φ z := by
  set ψ : ℝ → ℝ := fun z => (φ z).toReal
  -- three-slope inequality in multiplied form
  have key : ∀ z w, 0 ≤ z → z < m → m < w → φ z < ⊤ → φ w < ⊤ →
      φ m < ⊤ ∧ (ψ m - ψ z) * (w - m) ≤ (ψ w - ψ m) * (m - z) := by
    intro z w hz hzm' hmw' hfz' hfw'
    set θ := (w - m) / (w - z)
    have hwz : 0 < w - z := by linarith
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hwz.le
    have hθ1 : θ ≤ 1 := (div_le_one hwz).2 (by linarith)
    have hm : θ * z + (1 - θ) * w = m := by simp only [θ]; field_simp; ring
    obtain ⟨h1, h2⟩ := conv_real hφ hz (by linarith) hθ0 hθ1 hfz' hfw'
    rw [hm] at h1 h2
    refine ⟨h1, ?_⟩
    have h3 : ψ m * (w - z) ≤ (w - m) * ψ z + (m - z) * ψ w := by
      have := mul_le_mul_of_nonneg_left h2 hwz.le
      have e1 : (w - z) * (θ * ψ z + (1 - θ) * ψ w) = (w - m) * ψ z + (m - z) * ψ w := by
        simp only [θ]; field_simp; ring
      simp only [ψ] at e1 ⊢
      nlinarith
    nlinarith
  obtain ⟨hfm, -⟩ := key z0 w0 hz0 hzm hmw hfz hfw
  refine ⟨hfm, ?_⟩
  set S := {s : ℝ | ∃ z, 0 ≤ z ∧ z < m ∧ φ z < ⊤ ∧ s = (ψ m - ψ z) / (m - z)}
  have hSne : S.Nonempty := ⟨_, z0, hz0, hzm, hfz, rfl⟩
  have hSle : ∀ w, m < w → φ w < ⊤ → ∀ s ∈ S, s ≤ (ψ w - ψ m) / (w - m) := by
    rintro w hw hfw' _ ⟨z, hz, hzm', hfz', rfl⟩
    have := (key z w hz hzm' hw hfz' hfw').2
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hSbdd : BddAbove S := ⟨_, hSle w0 hmw hfw⟩
  refine ⟨sSup S, fun z hz => ?_⟩
  by_cases hfz' : φ z = ⊤
  · rw [hfz']; exact le_top
  have hfz'' : φ z < ⊤ := lt_top_iff_ne_top.2 hfz'
  rw [fin_eq hφ hz hfz'', EReal.coe_le_coe_iff]
  rcases lt_trichotomy z m with h | h | h
  · have hs : (ψ m - ψ z) / (m - z) ≤ sSup S := le_csSup hSbdd ⟨z, hz, h, hfz'', rfl⟩
    rw [div_le_iff₀ (by linarith)] at hs
    simp only [ψ] at hs ⊢
    nlinarith
  · subst h; simp
  · have hs : sSup S ≤ (ψ z - ψ m) / (z - m) := csSup_le hSne (hSle z h hfz'')
    rw [le_div_iff₀ (by linarith)] at hs
    simp only [ψ] at hs ⊢
    nlinarith

/-- a global affine minorant -/
lemma minorant (hφ : IsPhiFunction φ) :
    ∃ α β : ℝ, ∀ z : ℝ, 0 ≤ z → ((α + β * z : ℝ) : EReal) ≤ φ z := by
  have hf1 : φ 1 < ⊤ := by rw [hφ.map_one]; exact EReal.zero_lt_top
  by_cases hL : ∃ z0, 0 ≤ z0 ∧ z0 < 1 ∧ φ z0 < ⊤
  · obtain ⟨z0, hz0, hz01, hfz0⟩ := hL
    by_cases hR : ∃ w0, 1 < w0 ∧ φ w0 < ⊤
    · obtain ⟨w0, hw0, hfw0⟩ := hR
      obtain ⟨hfm, c, hc⟩ := subgrad hφ hz0 hz01 hw0 hfz0 hfw0
      exact ⟨(φ 1).toReal - c * 1, c, fun z hz => by
        have := hc z hz; convert this using 2; ring⟩
    · push_neg at hR
      have hmid : z0 < (z0 + 1) / 2 := by linarith
      obtain ⟨hfm, c, hc⟩ := subgrad hφ hz0 hmid (by linarith : (z0 + 1) / 2 < 1) hfz0 hf1
      exact ⟨(φ ((z0 + 1) / 2)).toReal - c * ((z0 + 1) / 2), c, fun z hz => by
        have := hc z hz; convert this using 2; ring⟩
  · push_neg at hL
    by_cases hR : ∃ w0, 1 < w0 ∧ φ w0 < ⊤
    · obtain ⟨w0, hw0, hfw0⟩ := hR
      obtain ⟨hfm, c, hc⟩ := subgrad hφ zero_le_one (by linarith : (1:ℝ) < (1 + w0) / 2)
        (by linarith : (1 + w0) / 2 < w0) hf1 hfw0
      exact ⟨(φ ((1 + w0) / 2)).toReal - c * ((1 + w0) / 2), c, fun z hz => by
        have := hc z hz; convert this using 2; ring⟩
    · push_neg at hR
      refine ⟨0, 0, fun z hz => ?_⟩
      rcases lt_trichotomy z 1 with h | h | h
      · rw [top_le_iff.1 (hL z hz h)]; exact le_top
      · subst h; rw [hφ.map_one]; simp
      · rw [top_le_iff.1 (hR z h)]; exact le_top

/-- measurability of `φ ∘ Z` for nonnegative measurable `Z` -/
lemma meas_comp (hφ : IsPhiFunction φ) {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℝ}
    (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω) : Measurable (fun ω => φ (Z ω)) := by
  apply measurable_of_Iic
  intro c
  have : (fun ω => φ (Z ω)) ⁻¹' Iic c = Z ⁻¹' {z | 0 ≤ z ∧ φ z ≤ c} := by
    ext ω; simp [hZ0 ω]
  rw [this]
  refine hZ ?_
  apply Set.OrdConnected.measurableSet
  refine ⟨fun z1 hz1 z2 hz2 z hz => ⟨hz1.1.trans hz.1, ?_⟩⟩
  rcases eq_or_lt_of_le (hz.1.trans hz.2) with he | hlt
  · have : z = z1 := le_antisymm (he ▸ hz.2) hz.1
    rw [this]; exact hz1.2
  set θ := (z2 - z) / (z2 - z1)
  have hd : 0 < z2 - z1 := by linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hz.2]) hd.le
  have hθ1 : θ ≤ 1 := (div_le_one hd).2 (by linarith [hz.1])
  have hz' : θ * z1 + (1 - θ) * z2 = z := by simp only [θ]; field_simp; ring
  have hcv := hφ.convex z1 z2 θ hz1.1 (hz1.1.trans hlt.le) hθ0 hθ1
  rw [hz'] at hcv
  induction c using EReal.rec with
  | bot => exact absurd (le_bot_iff.1 hz1.2) (hφ.ne_bot z1 hz1.1)
  | top => exact le_top
  | coe r =>
    have hf1 : φ z1 < ⊤ := lt_of_le_of_lt hz1.2 (EReal.coe_lt_top r)
    have hf2 : φ z2 < ⊤ := lt_of_le_of_lt hz2.2 (EReal.coe_lt_top r)
    have h1 := (conv_real hφ hz1.1 (hz1.1.trans hlt.le) hθ0 hθ1 hf1 hf2)
    rw [hz'] at h1
    rw [fin_eq hφ (hz1.1.trans hz.1) h1.1, EReal.coe_le_coe_iff]
    have a1 : (φ z1).toReal ≤ r := by
      have := hz1.2; rw [fin_eq hφ hz1.1 hf1] at this; exact_mod_cast this
    have a2 : (φ z2).toReal ≤ r := by
      have := hz2.2; rw [fin_eq hφ (hz1.1.trans hlt.le) hf2] at this; exact_mod_cast this
    nlinarith [h1.2]


/-- Jensen's inequality on one set, as a supporting-line bound -/
lemma set_jensen (hφ : IsPhiFunction φ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ0 : ∀ ω, 0 ≤ Z ω) (hZi : Integrable Z P)
    {B : Set Ω} (hB : MeasurableSet B) (hp : 0 < P.real B)
    (hfin : ∀ᵐ ω ∂P, ω ∈ B → φ (Z ω) < ⊤) {m : ℝ} (hm : m * P.real B = ∫ ω in B, Z ω ∂P) :
    φ m < ⊤ ∧ ∃ c : ℝ, ∀ᵐ ω ∂P, ω ∈ B → (((φ m).toReal + c * (Z ω - m) : ℝ) : EReal) ≤ φ (Z ω) := by
  have hm0 : 0 ≤ m := by
    have : 0 ≤ ∫ ω in B, Z ω ∂P := setIntegral_nonneg hB (fun ω _ => hZ0 ω)
    rw [← hm] at this
    exact nonneg_of_mul_nonneg_left this hp
  have hfin' : ∀ᵐ ω ∂P.restrict B, φ (Z ω) < ⊤ := (ae_restrict_iff' hB).2 hfin
  have hne : P.restrict B ≠ 0 := by
    intro h
    have : P.restrict B univ = 0 := by rw [h]; rfl
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at this
    have : P.real B = 0 := by simp [measureReal_def, this]
    linarith
  haveI : (ae (P.restrict B)).NeBot := ae_neBot.2 hne
  -- degenerate case: `Z = m` a.e. on `B`
  have degen : (∀ᵐ ω ∂P.restrict B, Z ω = m) →
      φ m < ⊤ ∧ ∃ c : ℝ, ∀ᵐ ω ∂P, ω ∈ B →
        (((φ m).toReal + c * (Z ω - m) : ℝ) : EReal) ≤ φ (Z ω) := by
    intro hZm
    obtain ⟨ω, h1, h2⟩ := (hZm.and hfin').exists
    have hfm : φ m < ⊤ := h1 ▸ h2
    refine ⟨hfm, 0, (ae_restrict_iff' hB).1 (hZm.mono fun ω hω => ?_)⟩
    rw [hω, fin_eq hφ hm0 hfm]; simp
  have hint : ∫ ω in B, (Z ω - m) ∂P = 0 := by
    rw [integral_sub hZi.integrableOn (integrable_const m), setIntegral_const, ← hm]
    simp [smul_eq_mul]; ring
  by_cases hL : ∃ z0, 0 ≤ z0 ∧ z0 < m ∧ φ z0 < ⊤
  · by_cases hR : ∃ w0, m < w0 ∧ φ w0 < ⊤
    · obtain ⟨z0, hz0, hz0m, hfz0⟩ := hL
      obtain ⟨w0, hw0, hfw0⟩ := hR
      obtain ⟨hfm, c, hc⟩ := subgrad hφ hz0 hz0m hw0 hfz0 hfw0
      exact ⟨hfm, c, Filter.Eventually.of_forall fun ω _ => hc (Z ω) (hZ0 ω)⟩
    · push_neg at hR
      apply degen
      have hle : ∀ᵐ ω ∂P.restrict B, Z ω ≤ m := hfin'.mono fun ω hω => by
        by_contra h; push_neg at h; exact absurd (hR _ h) (not_le.2 hω)
      have h0 : 0 ≤ᵐ[P.restrict B] fun ω => m - Z ω := hle.mono fun ω hω => by simp; linarith
      have hint' : ∫ ω in B, (m - Z ω) ∂P = 0 := by
        have : (fun ω => m - Z ω) = fun ω => -(Z ω - m) := by funext; ring
        rw [this, integral_neg, hint, neg_zero]
      have := (setIntegral_eq_zero_iff_of_nonneg_ae h0
        ((integrable_const m).sub hZi).integrableOn).1 hint'
      exact this.mono fun ω hω => by simp at hω; linarith
  · push_neg at hL
    apply degen
    have hge : ∀ᵐ ω ∂P.restrict B, m ≤ Z ω := hfin'.mono fun ω hω => by
      by_contra h; push_neg at h; exact absurd (hL _ (hZ0 ω) h) (not_le.2 hω)
    have h0 : 0 ≤ᵐ[P.restrict B] fun ω => Z ω - m := hge.mono fun ω hω => by simp; linarith
    have := (setIntegral_eq_zero_iff_of_nonneg_ae h0 (hZi.sub (integrable_const m)).integrableOn).1 hint
    exact this.mono fun ω hω => by simp at hω; linarith


/-- Jensen bound: every member of the ball satisfies the two-point inequality -/
lemma upper (hφ : IsPhiFunction φ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {δ : ℝ} {Q : Measure Ω} (hQ : Q ∈ phiBall φ P δ) {A : Set Ω}
    (hA : MeasurableSet A) (hx0 : 0 < P.real A) (hx1 : P.real A < 1) :
    ((P.real A : ℝ) : EReal) * φ (Q.real A / P.real A) +
      ((1 - P.real A : ℝ) : EReal) * φ ((1 - Q.real A) / (1 - P.real A)) ≤ (δ : EReal) := by
  obtain ⟨hQp, hQP, hD⟩ := hQ
  set Z : Ω → ℝ := fun ω => (Q.rnDeriv P ω).toReal with hZdef
  have hZm : Measurable Z := (Measure.measurable_rnDeriv Q P).ennreal_toReal
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => ENNReal.toReal_nonneg
  have hZi : Integrable Z P := Measure.integrable_toReal_rnDeriv
  have hZB : ∀ B, ∫ ω in B, Z ω ∂P = Q.real B := fun B => Measure.setIntegral_toReal_rnDeriv hQP B
  set u : Ω → EReal := fun ω => φ (Z ω) with hudef
  have hu : Measurable u := meas_comp hφ hZm hZ0
  set pos : Ω → ℝ≥0∞ := fun ω => (u ω).toENNReal with hposdef
  set neg : Ω → ℝ≥0∞ := fun ω => (-u ω).toENNReal with hnegdef
  have hpos_m : Measurable pos := EReal.continuous_toENNReal.measurable.comp hu
  have hneg_m : Measurable neg :=
    EReal.continuous_toENNReal.measurable.comp (continuous_neg.measurable.comp hu)
  have hD' : phiDiv φ Q P = ((∫⁻ ω, pos ω ∂P : ℝ≥0∞) : EReal) - ((∫⁻ ω, neg ω ∂P : ℝ≥0∞) : EReal) :=
    rfl
  obtain ⟨α, β, hαβ⟩ := minorant hφ
  have hN : ∫⁻ ω, neg ω ∂P ≠ ⊤ := by
    have hint : Integrable (fun ω => |α| + |β| * Z ω) P := (integrable_const _).add (hZi.const_mul _)
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => ?_) hint.lintegral_lt_top)
    have h := hαβ (Z ω) (hZ0 ω)
    have h2 : -u ω ≤ ((|α| + |β| * Z ω : ℝ) : EReal) := by
      have : -u ω ≤ -(((α + β * Z ω : ℝ)) : EReal) := EReal.neg_le_neg_iff.2 h
      refine this.trans ?_
      rw [← EReal.coe_neg, EReal.coe_le_coe_iff]
      have := hZ0 ω
      nlinarith [neg_abs_le α, neg_abs_le β, abs_nonneg β]
    exact (EReal.toENNReal_le_toENNReal h2).trans_eq (EReal.real_coe_toENNReal _)
  have hPp : ∫⁻ ω, pos ω ∂P ≠ ⊤ := by
    intro h
    rw [hD', h, EReal.coe_ennreal_top, EReal.top_sub (by rwa [ne_eq, EReal.coe_ennreal_eq_top_iff])] at hD
    exact absurd hD (not_le.2 (EReal.coe_lt_top δ))
  have hfinae : ∀ᵐ ω ∂P, u ω < ⊤ := (ae_lt_top hpos_m hPp).mono fun ω h =>
    lt_top_iff_ne_top.2 (EReal.toENNReal_ne_top_iff.1 h.ne)
  set r : Ω → ℝ := fun ω => (pos ω).toReal - (neg ω).toReal with hrdef
  have hri : Integrable r P := (integrable_toReal_of_lintegral_ne_top hpos_m.aemeasurable hPp).sub
    (integrable_toReal_of_lintegral_ne_top hneg_m.aemeasurable hN)
  have hDr : phiDiv φ Q P = ((∫ ω, r ω ∂P : ℝ) : EReal) := by
    rw [hD', integral_sub (integrable_toReal_of_lintegral_ne_top hpos_m.aemeasurable hPp)
      (integrable_toReal_of_lintegral_ne_top hneg_m.aemeasurable hN),
      integral_toReal hpos_m.aemeasurable (ae_lt_top hpos_m hPp),
      integral_toReal hneg_m.aemeasurable (ae_lt_top hneg_m hN), EReal.coe_sub,
      EReal.coe_ennreal_toReal hPp, EReal.coe_ennreal_toReal hN]
  have hur : ∀ᵐ ω ∂P, u ω = ((r ω : ℝ) : EReal) := hfinae.mono fun ω h => by
    have hy : u ω = (((u ω).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal h.ne (hφ.ne_bot _ (hZ0 ω))).symm
    simp only [r, pos, neg]
    rw [hy, ← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
      ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', max_zero_sub_max_neg_zero_eq_self]
  -- the bound on one set
  have hset : ∀ B, MeasurableSet B → 0 < P.real B →
      φ (Q.real B / P.real B) < ⊤ ∧
        P.real B * (φ (Q.real B / P.real B)).toReal ≤ ∫ ω in B, r ω ∂P := by
    intro B hB hp
    set m := Q.real B / P.real B
    have hm : m * P.real B = ∫ ω in B, Z ω ∂P := by
      rw [hZB]; exact div_mul_cancel₀ _ hp.ne'
    obtain ⟨hfm, c, hc⟩ := set_jensen hφ hZ0 hZi hB hp (hfinae.mono fun ω h _ => h) hm
    refine ⟨hfm, ?_⟩
    have hle : (fun ω => ((φ m).toReal - c * m) + c * Z ω) ≤ᵐ[P.restrict B] r := by
      rw [Filter.EventuallyLE, ae_restrict_iff' hB]
      filter_upwards [hc, hur] with ω h1 h2 hωB
      have := h1 hωB
      have h2' : φ (Z ω) = ((r ω : ℝ) : EReal) := h2
      rw [h2', EReal.coe_le_coe_iff] at this
      linarith
    have hl := setIntegral_mono_ae_restrict (f := fun ω => ((φ m).toReal - c * m) + c * Z ω)
      (((integrable_const _).add (hZi.const_mul c)).integrableOn) hri.integrableOn hle
    rw [integral_add (integrable_const _).integrableOn (hZi.const_mul c).integrableOn,
      setIntegral_const, integral_const_mul, hZB] at hl
    have hQB : Q.real B = m * P.real B := by rw [hm, hZB]
    rw [hQB, smul_eq_mul] at hl
    nlinarith
  obtain ⟨hfa, ha⟩ := hset A hA hx0
  have hpc : P.real Aᶜ = 1 - P.real A := probReal_compl_eq_one_sub hA
  have hqc : Q.real Aᶜ = 1 - Q.real A := probReal_compl_eq_one_sub hA
  obtain ⟨hfb, hb⟩ := hset Aᶜ hA.compl (by rw [hpc]; linarith)
  rw [hpc, hqc] at hfb hb
  have htot : ∫ ω, r ω ∂P = (∫ ω in A, r ω ∂P) + ∫ ω in Aᶜ, r ω ∂P :=
    (integral_add_compl hA hri).symm
  rw [fin_eq hφ (div_nonneg measureReal_nonneg hx0.le) hfa,
    fin_eq hφ (div_nonneg (by linarith [measureReal_le_one (μ := Q) (s := A)])
      (by linarith)) hfb]
  have e : ((P.real A : ℝ) : EReal) * ((φ (Q.real A / P.real A)).toReal : EReal) +
      ((1 - P.real A : ℝ) : EReal) * ((φ ((1 - Q.real A) / (1 - P.real A))).toReal : EReal) =
      ((P.real A * (φ (Q.real A / P.real A)).toReal +
        (1 - P.real A) * (φ ((1 - Q.real A) / (1 - P.real A))).toReal : ℝ) : EReal) := by
    simp only [EReal.coe_add, EReal.coe_mul]
  rw [e]
  refine le_trans ?_ (hDr ▸ hD)
  rw [EReal.coe_le_coe_iff, htot]
  linarith


lemma lint_pw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (u v : ℝ≥0∞) {f : Ω → ℝ≥0∞} (hf : f =ᵐ[P] A.piecewise (fun _ => u) (fun _ => v)) :
    ∫⁻ ω, f ω ∂P = u * P A + v * P Aᶜ := by
  rw [lintegral_congr_ae hf, ← lintegral_add_compl _ hA,
    setLIntegral_congr_fun hA (g := fun _ => u) (fun ω hω => Set.piecewise_eq_of_mem _ _ _ hω),
    setLIntegral_congr_fun hA.compl (g := fun _ => v)
      (fun ω hω => Set.piecewise_eq_of_notMem _ _ _ hω),
    setLIntegral_const, setLIntegral_const]

lemma mul_ne_bot_of_pos {y : ℝ} (hy : 0 < y) {e : EReal} (he : e ≠ ⊥) : (y : EReal) * e ≠ ⊥ := by
  induction e using EReal.rec with
  | bot => exact absurd rfl he
  | top => rw [EReal.coe_mul_top_of_pos hy]; simp
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

/-- the extremal two-point measures lie in the ball -/
lemma lower (hφ : IsPhiFunction φ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {δ : ℝ} {A : Set Ω} (hA : MeasurableSet A) (hx0 : 0 < P.real A)
    (hx1 : P.real A < 1) {t : ℝ} (ht : t ∈ Icc (P.real A) 1)
    (hE : ((P.real A : ℝ) : EReal) * φ (t / P.real A) +
      ((1 - P.real A : ℝ) : EReal) * φ ((1 - t) / (1 - P.real A)) ≤ (δ : EReal)) :
    ∃ Q ∈ phiBall φ P δ, Q.real A = t := by
  classical
  set x := P.real A with hxdef
  set a := t / x with hadef
  set b := (1 - t) / (1 - x) with hbdef
  have hx1' : 0 < 1 - x := by linarith
  have ht0 : 0 ≤ t := hx0.le.trans ht.1
  have ha0 : 0 ≤ a := div_nonneg ht0 hx0.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith [ht.2]) hx1'.le
  have hfa : φ a < ⊤ := by
    by_contra h
    rw [not_lt_top_iff.1 h, EReal.coe_mul_top_of_pos hx0,
      EReal.top_add_of_ne_bot (mul_ne_bot_of_pos hx1' (hφ.ne_bot b hb0))] at hE
    exact absurd hE (not_le.2 (EReal.coe_lt_top δ))
  have hfb : φ b < ⊤ := by
    by_contra h
    rw [not_lt_top_iff.1 h, EReal.coe_mul_top_of_pos hx1',
      EReal.add_top_of_ne_bot (mul_ne_bot_of_pos hx0 (hφ.ne_bot a ha0))] at hE
    exact absurd hE (not_le.2 (EReal.coe_lt_top δ))
  set A1 := (φ a).toReal
  set B1 := (φ b).toReal
  have hE' : x * A1 + (1 - x) * B1 ≤ δ := by
    rw [fin_eq hφ ha0 hfa, fin_eq hφ hb0 hfb] at hE
    have e : ((x : ℝ) : EReal) * ((A1 : ℝ) : EReal) + ((1 - x : ℝ) : EReal) * ((B1 : ℝ) : EReal) =
        ((x * A1 + (1 - x) * B1 : ℝ) : EReal) := by simp only [EReal.coe_add, EReal.coe_mul]
    rw [e] at hE; exact_mod_cast hE
  set dens : Ω → ℝ≥0∞ := A.piecewise (fun _ => ENNReal.ofReal a) (fun _ => ENNReal.ofReal b)
  have hdm : Measurable dens := Measurable.piecewise hA measurable_const measurable_const
  set Q := P.withDensity dens with hQdef
  have hPA : P A = ENNReal.ofReal x := (ofReal_measureReal).symm
  have hPAc : P Aᶜ = ENNReal.ofReal (1 - x) := by
    rw [← probReal_compl_eq_one_sub hA]; exact (ofReal_measureReal).symm
  have hQA : Q A = ENNReal.ofReal t := by
    rw [hQdef, withDensity_apply _ hA, setLIntegral_congr_fun hA (g := fun _ => ENNReal.ofReal a)
      (fun ω hω => Set.piecewise_eq_of_mem _ _ _ hω), setLIntegral_const, hPA,
      ← ENNReal.ofReal_mul ha0]
    congr 1; simp only [a]; field_simp
  have hQAc : Q Aᶜ = ENNReal.ofReal (1 - t) := by
    rw [hQdef, withDensity_apply _ hA.compl, setLIntegral_congr_fun hA.compl
      (g := fun _ => ENNReal.ofReal b) (fun ω hω => Set.piecewise_eq_of_notMem _ _ _ hω),
      setLIntegral_const, hPAc, ← ENNReal.ofReal_mul hb0]
    congr 1; simp only [b]; field_simp
  have hQprob : IsProbabilityMeasure Q := by
    constructor
    rw [← measure_add_measure_compl hA, hQA, hQAc, ← ENNReal.ofReal_add ht0 (by linarith [ht.2])]
    simp
  refine ⟨Q, ⟨hQprob, withDensity_absolutelyContinuous P dens, ?_⟩, ?_⟩
  · have hrn : ∀ᵐ ω ∂P, (Q.rnDeriv P ω).toReal = A.piecewise (fun _ => a) (fun _ => b) ω :=
      (Measure.rnDeriv_withDensity P hdm).mono fun ω h => by
        rw [h]
        by_cases hω : ω ∈ A
        · simp only [dens, Set.piecewise_eq_of_mem _ _ _ hω, ENNReal.toReal_ofReal ha0]
        · simp only [dens, Set.piecewise_eq_of_notMem _ _ _ hω, ENNReal.toReal_ofReal hb0]
    have hpos := lint_pw (P := P) hA (ENNReal.ofReal A1) (ENNReal.ofReal B1)
      (f := fun ω => (φ (Q.rnDeriv P ω).toReal).toENNReal) (hrn.mono fun ω h => by
        simp only [h]
        by_cases hω : ω ∈ A
        · simp only [Set.piecewise_eq_of_mem _ _ _ hω]; rw [fin_eq hφ ha0 hfa]; rfl
        · simp only [Set.piecewise_eq_of_notMem _ _ _ hω]; rw [fin_eq hφ hb0 hfb]; rfl)
    have hneg := lint_pw (P := P) hA (ENNReal.ofReal (-A1)) (ENNReal.ofReal (-B1))
      (f := fun ω => (-φ (Q.rnDeriv P ω).toReal).toENNReal) (hrn.mono fun ω h => by
        simp only [h]
        by_cases hω : ω ∈ A
        · simp only [Set.piecewise_eq_of_mem _ _ _ hω]; rw [fin_eq hφ ha0 hfa, ← EReal.coe_neg]; rfl
        · simp only [Set.piecewise_eq_of_notMem _ _ _ hω]; rw [fin_eq hφ hb0 hfb, ← EReal.coe_neg]
          rfl)
    unfold phiDiv
    have hne : ∀ p q : ℝ, ENNReal.ofReal p * ENNReal.ofReal x + ENNReal.ofReal q *
        ENNReal.ofReal (1 - x) ≠ ⊤ := fun p q =>
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
    have htr : ∀ p q : ℝ, (ENNReal.ofReal p * ENNReal.ofReal x + ENNReal.ofReal q *
        ENNReal.ofReal (1 - x)).toReal = max p 0 * x + max q 0 * (1 - x) := fun p q => by
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
        ENNReal.toReal_mul]
      simp only [ENNReal.toReal_ofReal', max_eq_left hx0.le, max_eq_left hx1'.le]
    rw [hpos, hneg, hPA, hPAc, ← EReal.coe_ennreal_toReal (hne _ _),
      ← EReal.coe_ennreal_toReal (hne _ _), htr, htr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h1 := max_zero_sub_max_neg_zero_eq_self A1
    have h2 := max_zero_sub_max_neg_zero_eq_self B1
    nlinarith
  · rw [measureReal_def, hQA, ENNReal.toReal_ofReal ht0]

end LRobP5Main

open LRobP5Main in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (φ : ℝ → EReal) (hφ : IsPhiFunction φ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ A : Set Ω, MeasurableSet A → upperProb (phiBall φ P δ) A = gPhi φ δ (P.real A) := by
  intro A hA
  have hPmem : P ∈ phiBall φ P δ := by
    refine ⟨inferInstance, Measure.AbsolutelyContinuous.rfl, ?_⟩
    have h1 : (∫⁻ ω, (φ (P.rnDeriv P ω).toReal).toENNReal ∂P) = 0 := by
      rw [lintegral_congr_ae ((Measure.rnDeriv_self P).mono fun ω hω => by
        dsimp only; rw [hω]; simp [hφ.map_one] : (fun ω => (φ (P.rnDeriv P ω).toReal).toENNReal) =ᵐ[P]
          fun _ => 0)]
      simp
    have h2 : (∫⁻ ω, (-(φ (P.rnDeriv P ω).toReal)).toENNReal ∂P) = 0 := by
      rw [lintegral_congr_ae ((Measure.rnDeriv_self P).mono fun ω hω => by
        dsimp only; rw [hω]; simp [hφ.map_one] : (fun ω => (-(φ (P.rnDeriv P ω).toReal)).toENNReal) =ᵐ[P]
          fun _ => 0)]
      simp
    unfold phiDiv
    rw [h1, h2]
    simp only [EReal.coe_ennreal_zero, sub_zero]
    exact_mod_cast hδ.le
  set V := (fun Q : Measure Ω => Q.real A) '' phiBall φ P δ with hVdef
  have hU : upperProb (phiBall φ P δ) A = sSup V := by
    unfold upperProb upperCap; rw [Set.image_image]; rfl
  rw [hU]
  have hVne : V.Nonempty := ⟨_, P, hPmem, rfl⟩
  have hVbdd : BddAbove V := ⟨1, by
    rintro _ ⟨Q, hQ, rfl⟩; haveI := hQ.1; exact measureReal_le_one⟩
  rcases (measureReal_nonneg : 0 ≤ P.real A).eq_or_lt with h0 | h0
  · have hPA : P A = 0 := by
      rw [eq_comm, measureReal_eq_zero_iff] at h0; exact h0
    have hV : V = {0} := by
      ext v; constructor
      · rintro ⟨Q, hQ, rfl⟩
        simp [measureReal_def, hQ.2.1 hPA]
      · rintro rfl; exact ⟨P, hPmem, by simp [measureReal_def, hPA]⟩
    rw [hV, csSup_singleton, ← h0]; simp [gPhi]
  rcases (measureReal_le_one : P.real A ≤ 1).eq_or_lt with h1 | h1
  · have hPAc : P Aᶜ = 0 := by
      have : P.real Aᶜ = 0 := by rw [probReal_compl_eq_one_sub hA, h1]; ring
      rwa [measureReal_eq_zero_iff] at this
    have hV : V = {1} := by
      ext v; constructor
      · rintro ⟨Q, hQ, rfl⟩
        haveI := hQ.1
        have hc : Q.real Aᶜ = 0 := by simp [measureReal_def, hQ.2.1 hPAc]
        rw [probReal_compl_eq_one_sub hA] at hc
        simp only [mem_singleton_iff]; linarith
      · rintro rfl; exact ⟨P, hPmem, h1⟩
    rw [hV, csSup_singleton, h1]; simp [gPhi]
  set x := P.real A with hxdef
  have hg : gPhi φ δ x = sSup {t : ℝ | t ∈ Set.Icc x 1 ∧
      (x : EReal) * φ (t / x) + ((1 - x : ℝ) : EReal) * φ ((1 - t) / (1 - x)) ≤ (δ : EReal)} := by
    unfold gPhi; rw [if_neg h0.ne', if_neg h1.ne]
  rw [hg]
  set T := {t : ℝ | t ∈ Set.Icc x 1 ∧
      (x : EReal) * φ (t / x) + ((1 - x : ℝ) : EReal) * φ ((1 - t) / (1 - x)) ≤ (δ : EReal)}
  have hxT : x ∈ T := by
    refine ⟨⟨le_rfl, h1.le⟩, ?_⟩
    rw [div_self h0.ne', div_self (by linarith : (1 - x) ≠ 0), hφ.map_one]
    simp only [mul_zero, add_zero]
    exact_mod_cast hδ.le
  have hTbdd : BddAbove T := ⟨1, fun t ht => ht.1.2⟩
  apply le_antisymm
  · refine csSup_le hVne ?_
    rintro _ ⟨Q, hQ, rfl⟩
    haveI := hQ.1
    by_cases hlt : Q.real A < x
    · exact hlt.le.trans (le_csSup hTbdd hxT)
    · exact le_csSup hTbdd ⟨⟨not_lt.1 hlt, measureReal_le_one⟩, upper hφ P hQ hA h0 h1⟩
  · refine csSup_le ⟨x, hxT⟩ ?_
    intro t ht
    obtain ⟨Q, hQ, hQt⟩ := lower hφ P hA h0 h1 ht.1 ht.2
    exact le_csSup hVbdd ⟨Q, hQ, hQt⟩
