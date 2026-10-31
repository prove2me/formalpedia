-- Prove2me | solution 1 for NetworkPricing.Caps.strong_nash_of_le_marginal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:02:37.04734+00:00
-- url     : https://prove2.me/submissions/3a5d7845-2816-414a-bfb5-56d054617b49

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model
import Theorems.Thm_NetworkPricing_Caps_lemma_1

open KellyStochasticNetworks NetworkPricing.Caps
open Set

theorem solution {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (tbar : Fin J → ℝ) (fstar : Fin R → ℝ) (hopt : I.IsOptimalToll flow fstar tbar)
    (hcap : ∀ e, tbar e ≤ I.marginalToll fstar e) :
    ∀ D : Finset (Fin J), ∀ t' : Fin J → ℝ, InCaps tbar t' → (∀ e ∉ D, t' e = tbar e) →
      ¬ ((∀ e ∈ D, I.profit flow tbar e ≤ I.profit flow t' e) ∧
          ∃ e ∈ D, I.profit flow tbar e < I.profit flow t' e) := by
  intro D t' hcaps hoff ⟨hall, e0, he0D, hstrict⟩
  have hA := hI.1
  have hconv := hI.2.2.2.2.2.2.1
  have hdiff := hI.2.2.2.2.2.2.2.1
  have lfnn : ∀ (g : Fin R → ℝ) (e : Fin J), (∀ q, 0 ≤ g q) → 0 ≤ linkFlow I.A g e := by
    intro g e hg
    unfold linkFlow
    apply Finset.sum_nonneg
    intro q _
    rcases hA e q with h | h <;> simp [h, hg q]
  have hex : ∃ e, t' e < tbar e := by
    by_contra hcon
    push Not at hcon
    have : t' = tbar := funext fun e => le_antisymm (hcaps.2 e) (hcon e)
    rw [this] at hstrict
    exact lt_irrefl _ hstrict
  obtain ⟨_, ⟨e, he, hL⟩⟩ := NetworkPricing.Caps.lemma_1 I hI hU flow hflow t' tbar hcaps.1 hopt.1
    hcaps.2 hex
  have heD : e ∈ D := by
    by_contra h
    rw [hoff e h] at he
    exact lt_irrefl _ he
  have hprof := hall e heD
  unfold Instance.profit at hprof
  have hlf : linkFlow I.A (flow tbar) e = linkFlow I.A fstar e := congrFun hopt.2.2 e
  have hc := hcap e
  unfold Instance.marginalToll at hc
  rw [← hlf] at hc
  set X := linkFlow I.A (flow tbar) e with hX
  set Y := linkFlow I.A (flow t') e with hY
  set d := deriv (I.ℓ e) X with hd
  have hXn : 0 ≤ X := lfnn _ e (hflow _ hopt.1).1.1
  have hYn : 0 ≤ Y := lfnn _ e (hflow _ hcaps.1).1.1
  have hs0 : 0 ≤ t' e := hcaps.1 e
  have hT : 0 < tbar e := lt_of_le_of_lt hs0 he
  have hXpos : 0 < X := by
    rcases lt_or_eq_of_le hXn with h | h
    · exact h
    · rw [← h] at hc; simp at hc; linarith
  have hdpos : 0 < d := by
    by_contra h; push Not at h
    nlinarith
  rcases le_or_gt Y X with hYX | hYX
  · have : t' e * Y ≤ t' e * X := mul_le_mul_of_nonneg_left hYX hs0
    have : t' e * X < tbar e * X := mul_lt_mul_of_pos_right he hXpos
    linarith
  · have h3 : 0 ≤ I.ℓ e X + tbar e - I.ℓ e Y - t' e := by
      by_contra hneg; push Not at hneg
      nlinarith
    have hsl := (hconv e).deriv_le_slope (show X ∈ Ici 0 from hXn) (show Y ∈ Ici 0 from hYn) hYX
      (hdiff e X)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hYX)] at hsl
    have h1 : d * (Y - X) ≤ tbar e - t' e := by rw [← hd] at hsl; linarith
    have h2 : d * (Y - X) * Y ≤ (tbar e - t' e) * Y := mul_le_mul_of_nonneg_right h1 hYn
    have h4 : tbar e * (Y - X) ≤ X * d * (Y - X) :=
      mul_le_mul_of_nonneg_right hc (sub_pos.mpr hYX).le
    have h5 : 0 < d * (Y - X) ^ 2 := mul_pos hdpos (pow_pos (sub_pos.mpr hYX) 2)
    nlinarith
