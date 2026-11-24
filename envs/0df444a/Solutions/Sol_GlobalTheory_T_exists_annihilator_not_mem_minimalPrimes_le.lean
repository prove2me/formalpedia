-- Prove2me | solution 1 for GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:53.604618+00:00
-- url     : https://prove2.me/submissions/cf9046ea-3dca-4c07-a415-8567cbcb32da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnnihilatorAvoidsFibreMinimalPrimesStatement
import Theorems.Thm_GlobalTheory_annihilator_avoids_fibre_minimalPrimes


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (b : B),
    (∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) →
    ∀ u : PrimeSpectrum B, ∃ g : B, g * b = 0 ∧ ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q := by
  first | exact @GlobalTheory.annihilator_avoids_fibre_minimalPrimes | exact GlobalTheory.annihilator_avoids_fibre_minimalPrimes | (intros; apply GlobalTheory.annihilator_avoids_fibre_minimalPrimes <;> assumption)
end _root_.GlobalTheory.T
