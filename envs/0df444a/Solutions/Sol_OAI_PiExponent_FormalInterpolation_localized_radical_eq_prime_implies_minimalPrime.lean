-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.localized_radical_eq_prime_implies_minimalPrime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:34:38.976438+00:00
-- url     : https://prove2.me/submissions/64b4dcc6-750e-4bdc-96cc-3512b54a658a

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

theorem solution
    {m n : Nat}
    (g : Fin n → MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hrad : Ideal.radical
      ((Ideal.span (Set.range g)).map
        (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
          (Localization.AtPrime P))) =
      P.map (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (Localization.AtPrime P))) :
    (Ideal.span (Set.range g)).IsMinimalPrime P := by
  have hdisj : ∀ Q : Ideal (MvPolynomial (Fin (m + 1)) Complex), Q ≤ P → Disjoint (P.primeCompl : Set (MvPolynomial (Fin (m + 1)) Complex)) Q := by
    intro Q hQ
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hx (hQ hxQ)
  have hcomap : ∀ Q : Ideal (MvPolynomial (Fin (m + 1)) Complex), Q.IsPrime → Q ≤ P →
      (Q.map (algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P))).comap
        (algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P)) = Q := fun Q hQ hle =>
    IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ (hdisj Q hle)
  have hIP : Ideal.span (Set.range g) ≤ P := by
    intro x hx
    have h1 : algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P) x ∈
        (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P)) := Ideal.mem_map_of_mem _ hx
    have h2 := Ideal.le_radical h1
    rw [hrad] at h2
    rw [← hcomap P inferInstance le_rfl]
    exact h2
  refine ⟨⟨inferInstance, hIP⟩, ?_⟩
  rintro Q ⟨hQ, hIQ⟩ hQP
  have hpr := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl
    (Localization.AtPrime P) Q hQ (hdisj Q hQP)
  have hle : (Ideal.span (Set.range g)).map (algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P)) ≤
      Q.map (algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P)) := Ideal.map_mono hIQ
  have hle2 := (Ideal.radical_mono hle).trans_eq hpr.radical
  rw [hrad] at hle2
  have := Ideal.comap_mono (f := algebraMap (MvPolynomial (Fin (m + 1)) Complex) (Localization.AtPrime P)) hle2
  rwa [hcomap P inferInstance le_rfl, hcomap Q hQ hQP] at this
