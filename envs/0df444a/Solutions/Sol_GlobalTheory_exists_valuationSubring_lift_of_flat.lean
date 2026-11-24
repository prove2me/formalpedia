-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_lift_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:43.067039+00:00
-- url     : https://prove2.me/submissions/0005f9ab-3f5d-47df-b532-28450c968726

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_exists_valuationSubring_lift_of_exists_le
import Theorems.Thm_GlobalTheory_exists_mem_le_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {O K : Type*} {A : Type u} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (m : Ideal A) [m.IsMaximal] (hmO : m.comap (algebraMap O A) = maximalIdeal O)
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hd : ∀ p : PrimeSpectrum A, p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O →
      p ∈ closure U) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : A →+* O'),
      (∀ a : O, (φ (algebraMap O A a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      (maximalIdeal O').comap φ = m ∧ PrimeSpectrum.comap φ ⊥ ∈ U :=
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  exists_valuationSubring_lift_of_exists_le m hmO hU (exists_mem_le_of_flat m hU hd)
end GlobalTheory
