-- Prove2me | solution 1 for Module.faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/b6aed03e-0e7b-5cb0-bb87-a79eb0e5421f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top

set_option autoImplicit false

universe u

theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (S' : Fin k → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra S (S' i)]
    [∀ i, Algebra (Localization.Away (r i)) (S' i)] [∀ i, IsScalarTower S (Localization.Away (r i)) (S' i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (r i)) (S' i)) :
    Module.FaithfullyFlat S (∀ i : Fin k, S' i) := by
  classical

  haveI : ∀ i, Module.Flat S (S' i) := fun i => by
    haveI : Module.Flat (Localization.Away (r i)) (S' i) := (hff i).toFlat
    haveI : Module.Flat S (Localization.Away (r i)) := IsLocalization.flat _ (Submonoid.powers (r i))
    exact Module.Flat.trans S (Localization.Away (r i)) (S' i)
  haveI : Module.Flat S (∀ i : Fin k, S' i) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype S (Fin k) (fun i => S' i)).symm
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
  haveI := hff i
  obtain ⟨q', hq'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Localization.Away (r i)) (B := S' i) q
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j : Fin k => S' j) i) q', ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have h1 : (Pi.evalRingHom (fun j : Fin k => S' j) i).comp (algebraMap S (∀ j : Fin k, S' j)) = algebraMap S (S' i) :=
    RingHom.ext fun _ => rfl
  rw [h1, IsScalarTower.algebraMap_eq S (Localization.Away (r i)) (S' i), PrimeSpectrum.comap_comp_apply, hq', hq]

end S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top
end P2MW
export P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top (solution)
