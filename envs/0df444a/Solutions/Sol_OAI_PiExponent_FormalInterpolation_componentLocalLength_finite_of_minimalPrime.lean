-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.componentLocalLength_finite_of_minimalPrime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:00:18.907989+00:00
-- url     : https://prove2.me/submissions/858f39c0-3b4b-48a9-a2b9-14c029f7a3e2

import Mathlib
import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

namespace A3S47LF

lemma finite_length {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I P : Ideal R) [P.IsPrime] (hmin : I.IsMinimalPrime P) :
    ∃ L : ℕ, componentLocalLength I P = (L : ENat) := by
  set Rp := Localization.AtPrime P
  set J : Ideal Rp := I.map (algebraMap R Rp)
  haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing P.primeCompl Rp inferInstance
  have hc : ∀ Q : Ideal (Rp ⧸ J), Q.IsPrime →
      Q.comap (Ideal.Quotient.mk J) = IsLocalRing.maximalIdeal Rp := by
    intro Q hQ
    set Q' : Ideal Rp := Q.comap (Ideal.Quotient.mk J)
    haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hJQ : J ≤ Q' := by
      intro a ha
      show Ideal.Quotient.mk J a ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact Q.zero_mem
    set q : Ideal R := Q'.comap (algebraMap R Rp)
    haveI : q.IsPrime := Ideal.comap_isPrime _ _
    have hIq : I ≤ q := Ideal.map_le_iff_le_comap.mp hJQ
    have hqP : q ≤ P := by
      have h1 : Q' ≤ IsLocalRing.maximalIdeal Rp := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top' )
      have h2 := Ideal.comap_mono (f := algebraMap R Rp) h1
      exact h2.trans (le_of_eq (Localization.AtPrime.under_maximalIdeal (I := P)))
    have hq : q = P := le_antisymm hqP (hmin.2 ⟨inferInstance, hIq⟩ hqP)
    rw [← IsLocalization.map_comap P.primeCompl Rp Q']
    show Ideal.map (algebraMap R Rp) q = _
    rw [hq, Localization.AtPrime.map_eq_maximalIdeal]
  have hK : Ring.KrullDimLE 0 (Rp ⧸ J) := by
    refine Ring.KrullDimLE.mk₀ (fun Q hQ => ?_)
    obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    have := hc M hM.isPrime
    rw [← hc Q hQ] at this
    have hMQ : M = Q := Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective this
    rw [← hMQ]; exact hM
  haveI : IsArtinianRing (Rp ⧸ J) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, hK⟩
  haveI : IsArtinian Rp (Rp ⧸ J) :=
    isArtinian_of_surjective_algebraMap (R := Rp ⧸ J) Ideal.Quotient.mk_surjective
  have hne : Module.length Rp (Rp ⧸ J) ≠ ⊤ := Module.length_ne_top
  obtain ⟨L, hL⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨L, hL.symm⟩

end A3S47LF

theorem solution
    {m : Nat}
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P) :
    ∃ L : Nat,
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
          (L : ENat) :=
  A3S47LF.finite_length _ P hminimal
