-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_lt_top_of_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:44.740803+00:00
-- url     : https://prove2.me/submissions/b0e02239-ff83-4263-a3ec-4fb3dbcd57f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing
namespace GlobalTheory
open IsLocalRing in
private theorem ringKrullDim_le_of_isLocalization (A D : Type) [CommRing A] [CommRing D]
    [Algebra A D] (M : Submonoid A) [IsLocalization M D] :
    ringKrullDim D ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D)) ?_
  refine Monotone.strictMono_of_injective (fun p q h => ?_)
    (PrimeSpectrum.localization_comap_injective D M)
  exact Ideal.comap_mono h
open IsLocalRing in
private theorem ringKrullDim_finite_of_finiteType_int (A : Type) [CommRing A]
    [Algebra.FiniteType ℤ A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective f.toRingHom hf) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have h : ((1 + Nat.card (Fin n) : ℕ) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  exact_mod_cast h
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D] :
    ringKrullDim D < ⊤ :=
  lt_of_le_of_lt
    (ringKrullDim_le_of_isLocalization (Algebra.EssFiniteType.subalgebra ℤ D) D
      (Algebra.EssFiniteType.submonoid ℤ D))
    (ringKrullDim_finite_of_finiteType_int _)
end _root_.GlobalTheory
end GlobalTheory
