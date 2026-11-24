-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:38:09.382855+00:00
-- url     : https://prove2.me/submissions/b873f849-531a-4690-86e1-ac41089758e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReduced

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
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] [IsReduced R] {y : R}
    (hy : ∀ P ∈ minimalPrimes R, y ∈ P) : y = 0 := by
  have : y ∈ nilradical R := by
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro J hJ
    haveI : Ideal.IsPrime J := hJ
    obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := J) bot_le
    exact hpJ (hy p hp)
  rw [nilradical_eq_zero] at this
  simpa using this
end GlobalTheory
