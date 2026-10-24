-- Prove2me | solution 1 for OAI.PiExponent.eventualLogJetSurjective_transverse_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:12:33.744887+00:00
-- url     : https://prove2.me/submissions/9c300fcc-d09e-41aa-ad40-721e7015253f

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_eventualLogJetSurjective_spatial_volume_bound
import Theorems.Thm_OAI_PiExponent_exists_positive_separatedWeights

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
    (K : ℚ) * alpha ^ m ≤ 1 := by
  obtain ⟨S, hS⟩ := hbase
  obtain ⟨w, hw, hsep⟩ :=
    OAI.PiExponent.exists_positive_separatedWeights m S
  let c : Fin K → Fin m → ℂ := fun j _ => (j.val : ℂ)
  have hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i) := by
    intro i a b hab
    apply Fin.ext
    exact_mod_cast (show (a.val : ℂ) = (b.val : ℂ) by simpa [c] using hab)
  exact OAI.PiExponent.eventualLogJetSurjective_spatial_volume_bound
    m K hm hK w0 v0 alpha hw0 hv0 halpha halpha1 w hw c hc
    (hS w hw hsep c hc)