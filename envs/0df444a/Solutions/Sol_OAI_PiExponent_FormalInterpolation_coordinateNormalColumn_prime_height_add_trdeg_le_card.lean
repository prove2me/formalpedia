-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_prime_height_add_trdeg_le_card
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:44:11.65101+00:00
-- url     : https://prove2.me/submissions/5a2d6e8a-2aae-48fd-97c6-ffee0f8ee6d1

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Field

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height + (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat ≤ m + 1 := by
  set A := MvPolynomial (Fin (m + 1)) Complex
  set B := A ⧸ P
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg Complex B
  letI : Algebra (MvPolynomial (Fin s) Complex) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower Complex (MvPolynomial (Fin s) Complex) B :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) Complex) B := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) Complex) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  -- transcendence degree bound
  have htrB : Algebra.trdeg Complex B = s := by
    have h := trdeg_add_eq (R := Complex) (S := MvPolynomial (Fin s) Complex) (A := B)
    haveI : Algebra.IsAlgebraic (MvPolynomial (Fin s) Complex) B := inferInstance
    rw [trdeg_eq_zero (R := MvPolynomial (Fin s) Complex) (A := B), add_zero,
      MvPolynomial.trdeg_of_isDomain] at h
    simpa using h.symm
  have htrL : Algebra.trdeg Complex (logarithmicPrimeField P) = s := by
    have hL : Algebra.trdeg B (logarithmicPrimeField P) = 0 := by
      have : Algebra.IsAlgebraic B (logarithmicPrimeField P) :=
        IsLocalization.isAlgebraic (logarithmicPrimeField P) (nonZeroDivisors B)
      exact trdeg_eq_zero
    have hadd := trdeg_add_eq (R := Complex) (S := B) (A := logarithmicPrimeField P)
    rw [hL, add_zero, htrB] at hadd
    exact hadd.symm
  rw [htrL, Cardinal.toNat_natCast]
  -- chain of length s above P
  have hdimS : ringKrullDim (MvPolynomial (Fin s) Complex) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨l, hl⟩ := (Order.le_krullDim_iff (α := PrimeSpectrum (MvPolynomial (Fin s) Complex))
    (n := s)).mp (by rw [← ringKrullDim, hdimS])
  obtain ⟨⟨Q, hQp, hQlo⟩⟩ := Ideal.nonempty_primesOver (S := B) l.head.asIdeal
  obtain ⟨L, hLlen, hLhead, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  have hmono : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk P)) := by
    intro a b hab
    refine lt_of_le_of_ne (fun x hx => (hab.le hx : _))  fun h => hab.ne ?_
    ext1
    have := congrArg PrimeSpectrum.asIdeal h
    simp only [PrimeSpectrum.comap_asIdeal] at this
    have := congrArg (Ideal.map (Ideal.Quotient.mk P)) this
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at this
  let L' := L.map _ hmono
  have hcoh : (s : ℕ∞) ≤ Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum A) := by
    have := Order.length_le_coheight (x := (⟨P, inferInstance⟩ : PrimeSpectrum A)) (p := L') (by
      show P ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk P) L.head).asIdeal
      rw [hLhead]
      intro x hx
      show Ideal.Quotient.mk P x ∈ Q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Q.zero_mem)
    simpa [L', hLlen, hl] using this
  have hdimA : ringKrullDim A = (m + 1 : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hsum : Order.height (⟨P, inferInstance⟩ : PrimeSpectrum A) +
      Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum A) ≤ (m + 1 : ℕ) := by
    have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum A)
    rw [← ringKrullDim, hdimA] at h
    have h2 : ((⨆ a : PrimeSpectrum A, Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞)
        = ((m + 1 : ℕ) : ℕ∞) := h.symm
    rw [WithBot.coe_inj] at h2
    rw [← h2]
    exact le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) _
  have hP : P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum A) :=
    PrimeSpectrum.height_eq_orderHeight ⟨P, inferInstance⟩
  rw [hP]
  calc _ ≤ Order.height (⟨P, inferInstance⟩ : PrimeSpectrum A) +
      Order.coheight (⟨P, inferInstance⟩ : PrimeSpectrum A) := by gcongr
    _ ≤ _ := by exact_mod_cast hsum
