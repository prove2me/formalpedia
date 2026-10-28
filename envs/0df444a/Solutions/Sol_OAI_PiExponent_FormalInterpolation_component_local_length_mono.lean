-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.component_local_length_mono
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:36:29.5684+00:00
-- url     : https://prove2.me/submissions/ccf4b45d-fc3e-4e75-b0be-0676b7173012

import Mathlib
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open OAI.PiExponent.FormalInterpolation

theorem solution : ¬ (∀ {R : Type} [CommRing R]
    (J I P : Ideal R) [P.IsPrime]
    (L : Nat)
    (hI : componentLocalLength I P = (L : ENat))
    (hJI : J ≤ I),
    ∃ M : Nat,
      componentLocalLength J P = (M : ENat) ∧ L ≤ M) := by
  intro h
  set P : Ideal ℤ := Ideal.span {2}
  haveI hP : P.IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  set Rp := Localization.AtPrime P
  have hI : componentLocalLength (⊤ : Ideal ℤ) P = ((0 : ℕ) : ENat) := by
    unfold componentLocalLength
    rw [Ideal.map_top]
    haveI : Subsingleton (Rp ⧸ (⊤ : Ideal Rp)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    simpa using Module.length_eq_zero (R := Rp) (M := Rp ⧸ (⊤ : Ideal Rp))
  obtain ⟨M, hM, -⟩ := h ⊥ ⊤ P 0 hI bot_le
  unfold componentLocalLength at hM
  rw [Ideal.map_bot] at hM
  have hne : Module.length Rp (Rp ⧸ (⊥ : Ideal Rp)) ≠ ⊤ := by rw [hM]; exact ENat.coe_ne_top M
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  haveI : IsArtinian Rp (Rp ⧸ (⊥ : Ideal Rp)) := hart
  haveI : IsArtinianRing Rp :=
    isArtinian_of_linearEquiv (Submodule.quotEquivOfEqBot (⊥ : Ideal Rp) rfl)
  haveI : Ring.KrullDimLE 0 Rp :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp inferInstance).2
  haveI : IsDomain Rp := inferInstance
  haveI : (⊥ : Ideal Rp).IsPrime := Ideal.bot_prime
  have hmax : (⊥ : Ideal Rp).IsMaximal := inferInstance
  have hbot : IsLocalRing.maximalIdeal Rp = ⊥ := (IsLocalRing.eq_maximalIdeal hmax).symm
  have hcomap := Localization.AtPrime.under_maximalIdeal (I := P)
  rw [hbot] at hcomap
  have h2 : (2 : ℤ) ∈ P := Ideal.subset_span rfl
  rw [← hcomap] at h2
  have h2' : algebraMap ℤ Rp 2 = 0 := h2
  have hinj := IsLocalization.injective Rp (Ideal.primeCompl_le_nonZeroDivisors P)
  have : (2 : ℤ) = 0 := hinj (by rw [h2', map_zero])
  norm_num at this
