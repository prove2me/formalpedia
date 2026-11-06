-- Prove2me | solution 2 for OAI.SevenEighths.CharacterTransport.primitive_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:41.687204+00:00
-- url     : https://prove2.me/submissions/022d1741-0fa4-49d9-9931-f828c5b42cd2

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

theorem solution (e : R ≃+* S) (χ : MulChar S ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : IsPrimitiveOnIdeals (pullback e χ) := by
  intro I hI
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hne : I.comap e.symm.toRingHom ≠ ⊥ := by
    intro h
    have : e x ∈ I.comap e.symm.toRingHom := by simpa using hxI
    rw [h] at this
    exact hx0 (by simpa using this)
  obtain ⟨u, hu1, hu2⟩ := hχ _ hne
  refine ⟨Units.map e.symm.toMonoidHom u, ?_, ?_⟩
  · simpa using hu1
  · simpa [pullback] using hu2
