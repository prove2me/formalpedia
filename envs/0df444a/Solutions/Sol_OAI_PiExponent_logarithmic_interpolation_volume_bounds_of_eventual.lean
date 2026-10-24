-- Prove2me | solution 1 for OAI.PiExponent.logarithmic_interpolation_volume_bounds_of_eventual
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:05:37.421998+00:00
-- url     : https://prove2.me/submissions/13cacadb-67b3-45e4-8896-6600f992e3fc

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_eventualLogJetSurjective_transverse_volume_bound
import Theorems.Thm_OAI_PiExponent_eventualLogJetSurjective_full_volume_bound

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
    (K : ℚ) * alpha ^ m ≤ 1 ∧
      (K : ℚ) * (w0 / v0) * alpha ^ m ≤ 1 := by
  exact ⟨
    OAI.PiExponent.eventualLogJetSurjective_transverse_volume_bound
      m K hm hK w0 v0 alpha hw0 hv0 halpha halpha1 hbase,
    OAI.PiExponent.eventualLogJetSurjective_full_volume_bound
      m K hm hK w0 v0 alpha hw0 hv0 halpha halpha1 hbase⟩