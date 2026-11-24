-- Prove2me | solution 1 for GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:36.228944+00:00
-- url     : https://prove2.me/submissions/5fe92795-8c79-4179-9a57-13564e050d1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Theorems.Thm_GlobalTheory_comap_eq_maximalIdeal_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct
namespace GlobalTheory
theorem _root_.solution (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] : Finite (MaximalSpectrum S) := by
  have hfin := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S)
    (maximalIdeal R)).to_subtype
  refine Finite.of_injective (β := (maximalIdeal R).primesOver S) (fun n ↦ ⟨n.asIdeal,
    n.isMaximal.isPrime, ⟨(have := n.isMaximal; (comap_eq_maximalIdeal_of_finite n.asIdeal).symm)⟩⟩)
    fun a b h ↦ MaximalSpectrum.ext congr(($h).1)
end GlobalTheory
