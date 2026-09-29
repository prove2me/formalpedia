-- Prove2me | solution 1 for Module.faithfullyFlat_pi_localizationAway_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/15d1326d-2974-5274-b85d-f87b73957b83

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top

set_option autoImplicit false

universe u

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤) :
    Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) := by
  classical

  haveI : Module.Flat S (∀ i : Fin k, Localization.Away (r i)) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype S (Fin k) (fun i => Localization.Away (r i))).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_

  have hi : ∃ i, r i ∉ p.asIdeal := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Ideal.span (Set.range r) ≤ p.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
    rw [hr, top_le_iff] at this
    exact p.2.ne_top this
  obtain ⟨i, hi⟩ := hi

  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (r i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)]
    exact hi
  obtain ⟨q, hq⟩ := hp
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j : Fin k => Localization.Away (r j)) i) q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have : (Pi.evalRingHom (fun j : Fin k => Localization.Away (r j)) i).comp
      (algebraMap S (∀ j : Fin k, Localization.Away (r j))) = algebraMap S (Localization.Away (r i)) :=
    RingHom.ext fun _ => rfl
  rw [this, hq]

end S_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top
end P2MW
export P2MW.S_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top (solution)
