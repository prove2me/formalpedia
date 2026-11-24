-- Prove2me | solution 1 for GlobalTheory.DI.PhiClosed.d_alg_pow_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:31.709792+00:00
-- url     : https://prove2.me/submissions/42755d8a-a9b5-4e05-a9c4-6c6bd8e639e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed
import Theorems.Thm_GlobalTheory_DI_PhiClosed_d_alg_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.PhiClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.PhiClosed
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) : d (algebraMap K (ExteriorAlgebra K V) (c ^ p)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  rw [map_pow, hk, d_alg_pow d hd c k, ← hk, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
end GlobalTheory.DI.PhiClosed
