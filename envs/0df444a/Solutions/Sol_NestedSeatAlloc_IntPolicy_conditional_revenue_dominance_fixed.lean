-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.conditional_revenue_dominance_fixed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:58:36.775266+00:00
-- url     : https://prove2.me/submissions/da1e9abf-cc9c-4080-bcf7-08baaf072449

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_integrable_of_seat_model
import Theorems.Thm_condRevenue_three_branch
import Theorems.Thm_endpoint_secants_of_inSubdiff
import Theorems.Thm_normalized_mono_of_endpoint_secants
import Theorems.Thm_NestedSeatAlloc_IntPolicy_three_branch_policy_dominance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p q : ℕ → ℝ) (k : ℕ) (s y : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hq : IsProtectionPolicy q) (hk : 1 ≤ k)
    (hs : 0 ≤ s) (hy : 0 ≤ y)
    (hdom : ∀ t, 0 ≤ t →
      expRevenue P X f q k t ≤ expRevenue P X f p k t)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (hsub : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1))) :
    condRevenue P X f q (k + 1) y s ≤
      condRevenue P X f p (k + 1) y s := by
  letI : IsProbabilityMeasure P := hM.isProb
  have hInt (r : ℕ → ℝ) (hr : IsProtectionPolicy r)
      (t : ℝ) (ht : 0 ≤ t) :
      Integrable (fun ω => revenue f r (fun i => X i ω) k t) P := by
    have h := revenue_integrable_of_seat_model
      P X f r hM hr (k - 1) t ht
    simpa only [Nat.sub_add_cancel hk] using h
  have hQ := condRevenue_three_branch P X f q k hk
    (hq k hk) y s hy (hInt q hq s hs)
    (hInt q hq (q k) (hq k hk))
    (fun hsy => hInt q hq (s - y) hsy)
  have hP := condRevenue_three_branch P X f p k hk
    (hp k hk) y s hy (hInt p hp s hs)
    (hInt p hp (p k) (hp k hk))
    (fun hsy => hInt p hp (s - y) hsy)
  obtain ⟨hl, hr⟩ := endpoint_secants_of_inSubdiff
    (expRevenue P X f p k) (p k) (f (k + 1))
    (hp k hk) hconc hsub
  obtain ⟨hmon, hant⟩ := normalized_mono_of_endpoint_secants
    (expRevenue P X f p k) (p k) (f (k + 1))
    (hp k hk) hconc hl hr
  have hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ p k →
      expRevenue P X f p k u - f (k + 1) * u ≤
        expRevenue P X f p k v - f (k + 1) * v := by
    intro u v hu huv hva
    exact hmon (Set.mem_Icc.mpr ⟨hu, le_trans huv hva⟩)
      (Set.mem_Icc.mpr ⟨le_trans hu huv, hva⟩) huv
  have hright : ∀ u v, p k ≤ u → u ≤ v →
      expRevenue P X f p k v - f (k + 1) * v ≤
        expRevenue P X f p k u - f (k + 1) * u := by
    intro u v hau huv
    exact hant (Set.mem_Ici.mpr hau)
      (Set.mem_Ici.mpr (le_trans hau huv)) huv
  rw [hQ, hP]
  exact three_branch_policy_dominance
    (expRevenue P X f q k) (expRevenue P X f p k)
    (f (k + 1)) (p k) (q k) y s
    (hp k hk) (hq k hk) hy hs hdom hleft hright
