-- Prove2me | solution 1 for OAI.PiExponent.eventualLogJetSurjective_full_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:18:18.384033+00:00
-- url     : https://prove2.me/submissions/b6dccd00-5a1f-4c3e-826c-5f36c3df2bfe

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_eventualLogJetSurjective_volume_bound_fixed
import Theorems.Thm_OAI_PiExponent_exists_positive_separated_weights
import Theorems.Thm_OAI_PiExponent_exists_coordinatewise_injective_centers

open scoped BigOperators

theorem solution
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K)
    (w0 v0 alpha : ℚ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hbase :
      ∃ S : List ℕ → ℕ,
        ∀ w : Fin m → ℕ, (∀ i, 0 < w i) →
          OAI.PiExponent.separatedWeights S w →
          ∀ c : Fin K → Fin m → ℂ,
            (∀ i : Fin m, Function.Injective (fun j : Fin K => c j i)) →
            OAI.PiExponent.eventualLogJetSurjective m K w0 v0 alpha w c) :
    (K : ℚ) * (w0 / v0) * alpha ^ m ≤ 1 := by
  obtain ⟨S, hS⟩ := hbase
  obtain ⟨w, hw, hsep⟩ :=
    OAI.PiExponent.exists_positive_separated_weights S m hm
  obtain ⟨c, hc⟩ :=
    OAI.PiExponent.exists_coordinatewise_injective_centers m K
  have hreal : (K : ℝ) * (w0 / v0) * alpha ^ m ≤ 1 :=
    OAI.PiExponent.eventualLogJetSurjective_volume_bound_fixed
      m K hm hK w0 v0 alpha hw0 hv0 halpha halpha1 w hw c hc
      (hS w hw hsep c hc)
  exact_mod_cast hreal