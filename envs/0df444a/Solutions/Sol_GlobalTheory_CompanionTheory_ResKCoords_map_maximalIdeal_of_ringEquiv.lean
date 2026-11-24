-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ResKCoords.map_maximalIdeal_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T12:04:36.660905+00:00
-- url     : https://prove2.me/submissions/eae392d1-32ec-40af-8a1b-2fb3171158d8

import Mathlib

open IsLocalRing

theorem solution {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  haveI : IsLocalHom e.toRingHom :=
    { map_nonunit := fun a ha => by simpa using IsUnit.map e.symm.toRingHom ha }
  haveI : IsLocalHom e.symm.toRingHom :=
    { map_nonunit := fun a ha => by simpa using IsUnit.map e.toRingHom ha }
  apply le_antisymm
  · exact IsLocalRing.map_maximalIdeal_le e.toRingHom
  · have h := IsLocalRing.map_maximalIdeal_le e.symm.toRingHom
    have := Ideal.map_mono (f := e.toRingHom) h
    simpa [Ideal.map_map, RingEquiv.comp_symm, Ideal.map_id] using this
