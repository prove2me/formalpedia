-- Prove2me | solution 1 for GlobalTheory.DI.PhiClosed.d_smul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:20.925639+00:00
-- url     : https://prove2.me/submissions/72d123ca-0c2e-4703-9e4b-079dac5bf7d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed
import Theorems.Thm_GlobalTheory_DI_PhiClosed_d_alg_pow_char

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
    (hd : IsOddDer d) (c : K) (y : ExteriorAlgebra K V) : d (c ^ p • y) = c ^ p • d y := by
  rw [Algebra.smul_def, hd.mul, AlgHom.commutes, d_alg_pow_char p d hd c, zero_mul, zero_add,
    ← Algebra.smul_def]
end GlobalTheory.DI.PhiClosed
