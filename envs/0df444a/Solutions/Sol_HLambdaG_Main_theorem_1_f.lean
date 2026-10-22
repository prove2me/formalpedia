-- Prove2me | solution 1 for HLambdaG.Main.theorem_1_f
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:56:59.081285+00:00
-- url     : https://prove2.me/submissions/d4e0be72-2402-472e-b042-0dcbf68e48b0

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

set_option autoImplicit false

open scoped NNReal

namespace HLambdaG.Main.P5db

open Filter Topology

lemma F_le_FInfT (C : CumulativeInput) (s t : ℝ≥0) : C.F s t ≤ FInfT C t :=
  le_ciSup (C.bdd_s t) s

lemma F_le_FsInf (C : CumulativeInput) (s t : ℝ≥0) : C.F s t ≤ FsInf C s :=
  le_ciSup (C.bdd_t s) t

lemma FInfT_mono (C : CumulativeInput) : Monotone (FInfT C) := by
  intro t t' h
  exact ciSup_mono (C.bdd_s t') (fun s => C.mono_t s h)

lemma T_le_leftLim (τ : TimeChange) {u s : ℝ≥0} (h : u < s) : τ.T u ≤ leftLim τ s := by
  unfold leftLim
  apply le_csSup
  · refine ⟨τ.T s, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact τ.mono (le_of_lt hv)
  · exact ⟨u, h, rfl⟩

lemma leftLim_le (τ : TimeChange) (s : ℝ≥0) : leftLim τ s ≤ τ.T s := by
  unfold leftLim
  apply csSup_le'
  rintro _ ⟨v, hv, rfl⟩
  exact τ.mono (le_of_lt hv)

lemma tendsto_sub_one : Tendsto (fun s : ℝ≥0 => s - 1) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun a ha => le_tsub_of_add_le_right ha⟩

lemma tendsto_coe_nn : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b.toNNReal, fun a ha => Real.toNNReal_le_iff_le_coe.1 ha⟩

lemma leftLim_tendsto (τ : TimeChange) : Tendsto (leftLim τ) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (τ.tendsto.comp tendsto_sub_one)
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
  exact T_le_leftLim τ (tsub_lt_self hs one_pos)

lemma ratio_sub_one (τ : TimeChange) (lam : ℝ)
    (hT : Tendsto (fun s : ℝ≥0 => (τ.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹)) :
    Tendsto (fun s : ℝ≥0 => (τ.T (s - 1) : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹) := by
  have h1 := hT.comp tendsto_sub_one
  have h2 : Tendsto (fun s : ℝ≥0 => 1 - (s : ℝ)⁻¹) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_inv_atTop_zero.comp tendsto_coe_nn)
    simpa using this
  have h3 := h1.mul h2
  rw [mul_one] at h3
  apply h3.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ≥0)] with s hs
  have hs' : (1 : ℝ) < s := by exact_mod_cast hs
  have hs1 : ((s - 1 : ℝ≥0) : ℝ) = (s : ℝ) - 1 := by
    rw [NNReal.coe_sub hs.le]; simp
  have hs0 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  have hspos : (0 : ℝ) < s := by linarith
  simp only [Function.comp, hs1]
  field_simp

lemma leftLim_ratio (τ : TimeChange) (lam : ℝ)
    (hT : Tendsto (fun s : ℝ≥0 => (τ.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹)) :
    Tendsto (fun s : ℝ≥0 => (leftLim τ s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (ratio_sub_one τ lam hT) hT
  · filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
    apply div_le_div_of_nonneg_right _ (NNReal.coe_nonneg s)
    exact_mod_cast T_le_leftLim τ (tsub_lt_self hs one_pos)
  · filter_upwards with s
    apply div_le_div_of_nonneg_right _ (NNReal.coe_nonneg s)
    exact_mod_cast leftLim_le τ s

lemma key14 (C : CumulativeInput) (τ : TimeChange) (s : ℝ≥0) :
    (s : ℝ)⁻¹ * FInfT C (leftLim τ s) ≤
      G C s - (s : ℝ)⁻¹ * (C.F s (leftLim τ s) - FInfT C (leftLim τ s)) := by
  have hinv : (0 : ℝ) ≤ (s : ℝ)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_left (F_le_FsInf C s (leftLim τ s)) hinv
  unfold G
  rw [mul_sub]
  linarith

lemma key15 (C : CumulativeInput) (τ : TimeChange) (s : ℝ≥0) :
    G C s - (s : ℝ)⁻¹ * (FsInf C s - C.F s (τ.T s)) ≤ (s : ℝ)⁻¹ * FInfT C (τ.T s) := by
  have hinv : (0 : ℝ) ≤ (s : ℝ)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_left (F_le_FInfT C s (τ.T s)) hinv
  unfold G
  rw [mul_sub]
  linarith

lemma upper_aux (Φ : ℝ≥0 → ℝ) (hΦ : Monotone Φ) (L : ℝ≥0 → ℝ≥0) (lam c b : ℝ)
    (hlam : 0 < lam) (hc : lam < c)
    (hL : Tendsto (fun s : ℝ≥0 => (L s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (hb : ∀ᶠ s : ℝ≥0 in atTop, (s : ℝ)⁻¹ * Φ (L s) ≤ b) :
    ∀ᶠ t : ℝ≥0 in atTop, (t : ℝ)⁻¹ * Φ t ≤ c * b := by
  have hc0 : 0 < c := hlam.trans hc
  have hinv : c⁻¹ < lam⁻¹ := inv_strictAnti₀ hlam hc
  have hr := hL.eventually (lt_mem_nhds hinv)
  obtain ⟨S, hS⟩ := eventually_atTop.1 (hb.and hr)
  set c' : ℝ≥0 := ⟨c, hc0.le⟩ with hc'
  have hc'0 : 0 < c' := by
    show (0 : ℝ) < c
    exact hc0
  filter_upwards [eventually_ge_atTop (S / c'), eventually_gt_atTop (0 : ℝ≥0)] with t ht ht0
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hSs : S ≤ t * c' := (div_le_iff₀ hc'0).1 ht
  obtain ⟨hb', hr'⟩ := hS (t * c') hSs
  have hs_eq : ((t * c' : ℝ≥0) : ℝ) = (t : ℝ) * c := by
    push_cast; rfl
  rw [hs_eq] at hb' hr'
  have hspos : (0 : ℝ) < (t : ℝ) * c := mul_pos ht0' hc0
  have h1 : c⁻¹ * ((t : ℝ) * c) < (L (t * c') : ℝ) := (lt_div_iff₀ hspos).1 hr'
  have h2 : c⁻¹ * ((t : ℝ) * c) = t := by field_simp
  rw [h2] at h1
  have hle : t ≤ L (t * c') := by
    have : (t : ℝ) ≤ (L (t * c') : ℝ) := h1.le
    exact_mod_cast this
  have hb2 : Φ (L (t * c')) ≤ ((t : ℝ) * c) * b := (inv_mul_le_iff₀ hspos).1 hb'
  rw [inv_mul_le_iff₀ ht0']
  calc Φ t ≤ Φ (L (t * c')) := hΦ hle
    _ ≤ ((t : ℝ) * c) * b := hb2
    _ = (t : ℝ) * (c * b) := by ring

lemma lower_aux (Φ : ℝ≥0 → ℝ) (hΦ : Monotone Φ) (L : ℝ≥0 → ℝ≥0) (lam c b : ℝ)
    (hc0 : 0 < c) (hc : c < lam)
    (hL : Tendsto (fun s : ℝ≥0 => (L s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (hb : ∀ᶠ s : ℝ≥0 in atTop, b ≤ (s : ℝ)⁻¹ * Φ (L s)) :
    ∀ᶠ t : ℝ≥0 in atTop, c * b ≤ (t : ℝ)⁻¹ * Φ t := by
  have hinv : lam⁻¹ < c⁻¹ := inv_strictAnti₀ hc0 hc
  have hr := hL.eventually (gt_mem_nhds hinv)
  obtain ⟨S, hS⟩ := eventually_atTop.1 (hb.and hr)
  set c' : ℝ≥0 := ⟨c, hc0.le⟩ with hc'
  have hc'0 : 0 < c' := by
    show (0 : ℝ) < c
    exact hc0
  filter_upwards [eventually_ge_atTop (S / c'), eventually_gt_atTop (0 : ℝ≥0)] with t ht ht0
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hSs : S ≤ t * c' := (div_le_iff₀ hc'0).1 ht
  obtain ⟨hb', hr'⟩ := hS (t * c') hSs
  have hs_eq : ((t * c' : ℝ≥0) : ℝ) = (t : ℝ) * c := by
    push_cast; rfl
  rw [hs_eq] at hb' hr'
  have hspos : (0 : ℝ) < (t : ℝ) * c := mul_pos ht0' hc0
  have h1 : (L (t * c') : ℝ) < c⁻¹ * ((t : ℝ) * c) := (div_lt_iff₀ hspos).1 hr'
  have h2 : c⁻¹ * ((t : ℝ) * c) = t := by field_simp
  rw [h2] at h1
  have hle : L (t * c') ≤ t := by
    have : (L (t * c') : ℝ) ≤ (t : ℝ) := h1.le
    exact_mod_cast this
  have hb2 : ((t : ℝ) * c) * b ≤ Φ (L (t * c')) := (le_inv_mul_iff₀ hspos).1 hb'
  rw [le_inv_mul_iff₀ ht0']
  calc (t : ℝ) * (c * b) = ((t : ℝ) * c) * b := by ring
    _ ≤ Φ (L (t * c')) := hb2
    _ ≤ Φ t := hΦ hle

lemma squeeze_final (f : ℝ≥0 → ℝ) (x : ℝ) (lo hi : ℝ → ℝ)
    (hlo : Tendsto lo (𝓝 0) (𝓝 x)) (hhi : Tendsto hi (𝓝 0) (𝓝 x))
    (h : ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ t : ℝ≥0 in atTop, lo δ ≤ f t ∧ f t ≤ hi δ) :
    Tendsto f atTop (𝓝 x) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have e : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (a < lo δ ∧ δ < 1) ∧ δ ∈ Set.Ioi (0 : ℝ) :=
      (((hlo.eventually (lt_mem_nhds ha)).and (eventually_lt_nhds one_pos)).filter_mono
        nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
    obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := e.exists
    exact (h δ h3 h2).mono fun t ht => lt_of_lt_of_le h1 ht.1
  · intro a ha
    have e : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (hi δ < a ∧ δ < 1) ∧ δ ∈ Set.Ioi (0 : ℝ) :=
      (((hhi.eventually (gt_mem_nhds ha)).and (eventually_lt_nhds one_pos)).filter_mono
        nhdsWithin_le_nhds).and eventually_mem_nhdsWithin
    obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := e.exists
    exact (h δ h3 h2).mono fun t ht => lt_of_le_of_lt ht.2 h1

lemma dir1 (C : CumulativeInput) (τ₁ τ₂ : TimeChange) (lam : ℝ)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂) (h : ℝ) (hH : Tendsto (H C) atTop (𝓝 h)) :
    Tendsto (G C) atTop (𝓝 (h * lam⁻¹)) := by
  have hlo0 : Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹ * FInfT C (leftLim τ₁ s)) atTop
      (𝓝 (h * lam⁻¹)) := by
    have := (hH.comp (leftLim_tendsto τ₁)).mul (leftLim_ratio τ₁ lam hT₁)
    apply this.congr'
    filter_upwards [(leftLim_tendsto τ₁).eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ≥0)] with s hs hs0
    have hs' : (0 : ℝ) < (leftLim τ₁ s : ℝ) := by exact_mod_cast hs
    have hs0' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
    simp only [Function.comp, H]
    field_simp
  have hhi0 : Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹ * FInfT C (τ₂.T s)) atTop
      (𝓝 (h * lam⁻¹)) := by
    have := (hH.comp τ₂.tendsto).mul hT₂
    apply this.congr'
    filter_upwards [τ₂.tendsto.eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ≥0)] with s hs hs0
    have hs' : (0 : ℝ) < (τ₂.T s : ℝ) := by exact_mod_cast hs
    have hs0' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs0
    simp only [Function.comp, H]
    field_simp
  have hlo := hlo0.add h14
  have hhi := hhi0.add h15
  rw [add_zero] at hlo hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro s
    have := key14 C τ₁ s
    simp only
    linarith
  · intro s
    have := key15 C τ₂ s
    simp only
    linarith

lemma dir2 (C : CumulativeInput) (τ₁ τ₂ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂) (g : ℝ) (hG : Tendsto (G C) atTop (𝓝 g)) :
    Tendsto (H C) atTop (𝓝 (lam * g)) := by
  have hA := hG.sub h14
  have hB := hG.sub h15
  rw [sub_zero] at hA hB
  apply squeeze_final (H C) (lam * g) (fun δ => lam * (1 - δ) * (g - δ))
    (fun δ => lam * (1 + δ) * (g + δ))
  · exact Continuous.tendsto' (by fun_prop) 0 (lam * g) (by ring)
  · exact Continuous.tendsto' (by fun_prop) 0 (lam * g) (by ring)
  intro δ hδ hδ1
  have hup : ∀ᶠ t : ℝ≥0 in atTop, (t : ℝ)⁻¹ * FInfT C t ≤ lam * (1 + δ) * (g + δ) := by
    apply upper_aux (FInfT C) (FInfT_mono C) (leftLim τ₁) lam (lam * (1 + δ)) (g + δ) hlam
      (by nlinarith) (leftLim_ratio τ₁ lam hT₁)
    filter_upwards [hA.eventually (gt_mem_nhds (show g < g + δ by linarith))] with s hs
    have := key14 C τ₁ s
    linarith
  have hlow : ∀ᶠ t : ℝ≥0 in atTop, lam * (1 - δ) * (g - δ) ≤ (t : ℝ)⁻¹ * FInfT C t := by
    apply lower_aux (FInfT C) (FInfT_mono C) τ₂.T lam (lam * (1 - δ)) (g - δ)
      (by nlinarith) (by nlinarith) hT₂
    filter_upwards [hB.eventually (lt_mem_nhds (show g - δ < g by linarith))] with s hs
    have := key15 C τ₂ s
    linarith
  filter_upwards [hup, hlow] with t h1 h2
  exact ⟨h2, h1⟩

end HLambdaG.Main.P5db

open NNReal Filter Topology HLambdaG.Main in
theorem solution
    (C : CumulativeInput) (τ₁ τ₂ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂) :
    ((∃ h : ℝ, Tendsto (H C) atTop (𝓝 h)) ↔
      (∃ g : ℝ, Tendsto (G C) atTop (𝓝 g))) ∧
      ∀ h g : ℝ, Tendsto (H C) atTop (𝓝 h) →
        Tendsto (G C) atTop (𝓝 g) → h = lam * g := by
  refine ⟨⟨fun ⟨h, hh⟩ => ⟨_, P5db.dir1 C τ₁ τ₂ lam hT₁ h14 hT₂ h15 h hh⟩,
    fun ⟨g, hg⟩ => ⟨_, P5db.dir2 C τ₁ τ₂ lam hlam hT₁ h14 hT₂ h15 g hg⟩⟩, ?_⟩
  intro h g hh hg
  have e := tendsto_nhds_unique hg (P5db.dir1 C τ₁ τ₂ lam hT₁ h14 hT₂ h15 h hh)
  rw [e]
  field_simp
