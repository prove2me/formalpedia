-- Prove2me | solution 1 for NetworkPricing.Caps.nash_unique_of_le_marginal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:01:12.1635+00:00
-- url     : https://prove2.me/submissions/a4eb0e5a-1c3b-4ab1-844a-7d64f0c69953

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model
import Theorems.Thm_NetworkPricing_Caps_lemma_1
import Theorems.Thm_NetworkPricing_Caps_lemma_2

open KellyStochasticNetworks NetworkPricing.Caps
open Set Filter Topology

theorem solution {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (tbar : Fin J → ℝ) (fstar : Fin R → ℝ) (hopt : I.IsOptimalToll flow fstar tbar)
    (hcap : ∀ e, tbar e ≤ I.marginalToll fstar e) :
    ∀ t : Fin J → ℝ, I.IsCappedNash flow tbar t → t = tbar := by
  intro t ⟨⟨h0, hle⟩, hdev⟩
  have hA := hI.1
  have hconv := hI.2.2.2.2.2.2.1
  have hdiff := hI.2.2.2.2.2.2.2.1
  have lfnn : ∀ (g : Fin R → ℝ) (e : Fin J), (∀ q, 0 ≤ g q) → 0 ≤ linkFlow I.A g e := by
    intro g e hg
    unfold linkFlow
    apply Finset.sum_nonneg
    intro q _
    rcases hA e q with h | h <;> simp [h, hg q]
  by_contra hne
  have hex : ∃ e, t e < tbar e := by
    by_contra hcon
    push Not at hcon
    exact hne (funext fun e => le_antisymm (hle e) (hcon e))
  obtain ⟨⟨e, he, hL⟩, _⟩ := NetworkPricing.Caps.lemma_1 I hI hU flow hflow t tbar h0 hopt.1
    hle hex
  have hloc : IsLocalMaxOn (fun s : ℝ => I.profit flow (Function.update t e s) e)
      (Set.Ici 0) (t e) := by
    show ∀ᶠ s in 𝓝[Ici 0] (t e), _ ≤ _
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds he)] with s hs0 hs1
    rw [Function.update_eq_self]
    exact hdev e s hs0 (le_of_lt hs1)
  have hl2 := NetworkPricing.Caps.lemma_2 I hI hU flow hflow t h0 e hloc
  have hlf : linkFlow I.A (flow tbar) e = linkFlow I.A fstar e := congrFun hopt.2.2 e
  have hc := hcap e
  unfold Instance.marginalToll at hc
  rw [← hlf] at hc
  set X := linkFlow I.A (flow tbar) e with hX
  set Y := linkFlow I.A (flow t) e with hY
  have hXn : 0 ≤ X := lfnn _ e (hflow _ hopt.1).1.1
  have hs0 : 0 ≤ t e := h0 e
  have hT : 0 < tbar e := lt_of_le_of_lt hs0 he
  have hXpos : 0 < X := by
    rcases lt_or_eq_of_le hXn with h | h
    · exact h
    · rw [← h] at hc; simp at hc; linarith
  have hdpos : 0 < deriv (I.ℓ e) X := by
    by_contra h; push Not at h
    nlinarith
  have hmd : deriv (I.ℓ e) X ≤ deriv (I.ℓ e) Y :=
    (hconv e).monotoneOn_deriv (fun z _ => (hdiff e z)) (show X ∈ Ici 0 from hXn)
      (show Y ∈ Ici 0 from hXn.trans hL) hL
  have h1 : X * deriv (I.ℓ e) X ≤ Y * deriv (I.ℓ e) X := mul_le_mul_of_nonneg_right hL hdpos.le
  have h2 : Y * deriv (I.ℓ e) X ≤ Y * deriv (I.ℓ e) Y :=
    mul_le_mul_of_nonneg_left hmd (hXn.trans hL)
  linarith
