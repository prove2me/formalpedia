-- Prove2me | solution 1 for NetworkPricing.Caps.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T00:58:38.166798+00:00
-- url     : https://prove2.me/submissions/255edbcb-4391-4457-9aef-efadf3036f35

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model
import Theorems.Thm_NetworkPricing_Caps_lemma_1

open KellyStochasticNetworks NetworkPricing.Caps
open Filter Topology Set

theorem solution {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (t : Fin J → ℝ) (ht : 0 ≤ t) (e : Fin J)
    (hloc : IsLocalMaxOn (fun s : ℝ => I.profit flow (Function.update t e s) e) (Set.Ici 0) (t e)) :
    linkFlow I.A (flow t) e * deriv (I.ℓ e) (linkFlow I.A (flow t) e) ≤ t e := by
  have hA := hI.1
  have hmono := hI.2.2.2.2.2.1 e
  have hdiff := hI.2.2.2.2.2.2.2.1 e
  have lfnn : ∀ g : Fin R → ℝ, (∀ q, 0 ≤ g q) → 0 ≤ linkFlow I.A g e := by
    intro g hg
    unfold linkFlow
    apply Finset.sum_nonneg
    intro q _
    rcases hA e q with h | h <;> simp [h, hg q]
  set x := linkFlow I.A (flow t) e with hx
  have hxn : 0 ≤ x := lfnn _ (hflow t ht).1.1
  have hte : 0 ≤ t e := ht e
  set c := x * t e with hc
  -- the key inequality for every toll s slightly above t e
  have hupd_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ Function.update t e s := by
    intro s hs i
    show (0:ℝ) ≤ Function.update t e s i
    by_cases h : i = e
    · rw [h, Function.update_self]; exact hs
    · rw [Function.update_of_ne h]; exact ht i
  have hloc' : ∀ᶠ s in 𝓝[>] (t e),
      t e < s ∧ s * linkFlow I.A (flow (Function.update t e s)) e ≤ t e * x := by
    have h1 : ∀ᶠ s in 𝓝[>] (t e), I.profit flow (Function.update t e s) e ≤
        I.profit flow (Function.update t e (t e)) e :=
      Filter.Eventually.filter_mono (nhdsWithin_mono _ (fun s (hs : t e < s) =>
        (show (0:ℝ) ≤ s from hte.trans hs.le))) hloc
    filter_upwards [h1, self_mem_nhdsWithin] with s hs hs'
    refine ⟨hs', ?_⟩
    simpa [Instance.profit, x] using hs
  have key : ∀ s : ℝ, t e < s → s * linkFlow I.A (flow (Function.update t e s)) e ≤ t e * x →
      I.ℓ e x - I.ℓ e (c * s⁻¹) ≤ s - t e := by
    intro s hs hprof
    have hs0 : 0 < s := lt_of_le_of_lt hte hs
    have hle : t ≤ Function.update t e s := by
      intro i
      by_cases h : i = e
      · rw [h, Function.update_self]; exact hs.le
      · rw [Function.update_of_ne h]
    have hL := NetworkPricing.Caps.lemma_1 I hI hU flow hflow t (Function.update t e s) ht
      (hupd_nn s hs0.le) hle ⟨e, by simpa using hs⟩
    obtain ⟨⟨e₁, he₁, h₁⟩, ⟨e₂, he₂, h₂⟩⟩ := hL
    have he₁e : e₁ = e := by
      by_contra h; simp [h] at he₁
    have he₂e : e₂ = e := by
      by_contra h; simp [h] at he₂
    rw [he₁e] at h₁; rw [he₂e] at h₂
    simp only [Function.update_self] at h₁ h₂
    set y := linkFlow I.A (flow (Function.update t e s)) e with hy
    have hyn : 0 ≤ y := lfnn _ (hflow _ (hupd_nn s hs0.le)).1.1
    have hyc : y ≤ c * s⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hs0]; nlinarith
    rcases lt_or_eq_of_le h₁ with hlt | heq
    · have h3 : 0 ≤ I.ℓ e y + s - I.ℓ e x - t e := by
        by_contra hneg; push Not at hneg
        nlinarith
      have h4 : I.ℓ e y ≤ I.ℓ e (c * s⁻¹) :=
        hmono (show (0:ℝ) ≤ y from hyn) (show (0:ℝ) ≤ c * s⁻¹ from hyn.trans hyc) hyc
      linarith
    · have hx0 : x = 0 := by
        rw [heq] at hprof
        nlinarith
      have : c = 0 := by rw [hc, hx0, zero_mul]
      rw [this, zero_mul, hx0]
      linarith
  have hev : ∀ᶠ s in 𝓝[>] (t e), I.ℓ e x - I.ℓ e (c * s⁻¹) - (s - t e) ≤ 0 := by
    filter_upwards [hloc'] with s hs
    linarith [key s hs.1 hs.2]
  rcases lt_or_eq_of_le hte with htpos | htzero
  · -- t e > 0 : differentiate H(s) = ℓ x - ℓ (c / s) - (s - t e) at s = t e
    have hcx : c * (t e)⁻¹ = x := by rw [hc]; field_simp
    have hg : HasDerivAt (fun s : ℝ => c * s⁻¹) (c * -((t e) ^ 2)⁻¹) (t e) :=
      (hasDerivAt_inv htpos.ne').const_mul c
    have hl : HasDerivAt (I.ℓ e) (deriv (I.ℓ e) x) (c * (t e)⁻¹) := by
      rw [hcx]; exact (hdiff x).hasDerivAt
    have hcomp := hl.comp (t e) hg
    have hH : HasDerivAt (fun s : ℝ => I.ℓ e x - I.ℓ e (c * s⁻¹) - (s - t e))
        (0 - deriv (I.ℓ e) x * (c * -((t e) ^ 2)⁻¹) - (1 - 0)) (t e) :=
      ((hasDerivAt_const _ _).sub hcomp).sub ((hasDerivAt_id _).sub (hasDerivAt_const _ _))
    have hT := (hasDerivAt_iff_tendsto_slope.mp hH).mono_left
      (nhdsWithin_mono _ (show Ioi (t e) ⊆ {t e}ᶜ from fun s hs => ne_of_gt hs))
    have hle := le_of_tendsto hT (by
      filter_upwards [hev, self_mem_nhdsWithin] with s hs hs'
      rw [slope_def_field]
      have hs'' : (0:ℝ) < s - t e := sub_pos.mpr hs'
      have : I.ℓ e x - I.ℓ e (c * (t e)⁻¹) - (t e - t e) = 0 := by rw [hcx]; ring
      rw [this, sub_zero]
      exact div_nonpos_of_nonpos_of_nonneg hs hs''.le)
    have e1 : deriv (I.ℓ e) x * (c * -((t e) ^ 2)⁻¹) = -(x * deriv (I.ℓ e) x) / t e := by
      rw [hc]; field_simp
    rw [e1] at hle
    have : x * deriv (I.ℓ e) x / t e ≤ 1 := by
      have : -(x * deriv (I.ℓ e) x) / t e = -(x * deriv (I.ℓ e) x / t e) := by ring
      linarith
    exact (div_le_one htpos).mp this
  · -- t e = 0
    have hc0 : c = 0 := by rw [hc, ← htzero, mul_zero]
    have hle : I.ℓ e x - I.ℓ e 0 ≤ 0 := by
      have hT : Tendsto (fun s : ℝ => s) (𝓝[>] (t e)) (𝓝 0) := by
        rw [← htzero]; exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      refine ge_of_tendsto hT ?_
      filter_upwards [hev] with s hs
      rw [hc0, zero_mul, ← htzero] at hs
      linarith
    rcases lt_or_eq_of_le hxn with hxpos | hxzero
    · have hconst : ∀ z ∈ Ioo 0 x, slope (I.ℓ e) x z = 0 := by
        intro z hz
        have h1 : I.ℓ e 0 ≤ I.ℓ e z :=
          hmono (Set.mem_Ici.mpr (le_refl (0:ℝ))) (show z ∈ Ici 0 from hz.1.le) hz.1.le
        have h2 : I.ℓ e z ≤ I.ℓ e x :=
          hmono (show z ∈ Ici 0 from hz.1.le) (show x ∈ Ici 0 from hxn) hz.2.le
        have : I.ℓ e z = I.ℓ e x := by linarith
        simp [slope_def_field, this]
      have hT := (hasDerivAt_iff_tendsto_slope.mp (hdiff x).hasDerivAt).mono_left
        (nhdsWithin_mono _ (show Iio x ⊆ {x}ᶜ from fun s hs => ne_of_lt hs))
      have hT0 : Tendsto (slope (I.ℓ e) x) (𝓝[<] x) (𝓝 0) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [Ioo_mem_nhdsLT hxpos] with z hz
          exact (hconst z hz).symm)
      have hd := tendsto_nhds_unique hT hT0
      rw [hd, mul_zero]; exact hte
    · rw [← hxzero]; simp [← htzero]
