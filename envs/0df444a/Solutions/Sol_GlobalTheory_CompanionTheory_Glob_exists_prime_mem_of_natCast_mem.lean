-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.exists_prime_mem_of_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:43.938471+00:00
-- url     : https://prove2.me/submissions/376d8e2a-7712-4a7a-b66e-1b36f1ef43ba

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_DYdc5_main__7c2f5d5b8d5c
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferentStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTer
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob
namespace GlobalTheory.CompanionTheory.Glob
theorem _root_.solution {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (t : ℕ) (ht : t ≠ 0) (htP : (t : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ (p : R) ∈ P :=
  _root_.P2M_UpperTheory_Reformulated_B_DYdc5_main__7c2f5d5b8d5c P t ht htP
end GlobalTheory.CompanionTheory.Glob
