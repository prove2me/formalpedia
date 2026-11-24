-- Prove2me | solution 1 for GlobalTheory.DI.PhiClosed.Dtot_smul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:42.989147+00:00
-- url     : https://prove2.me/submissions/c9d0854f-f31f-4359-8269-136674c40ef9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed
import Theorems.Thm_GlobalTheory_DI_PhiClosed_d_smul_pow

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
    (hd : IsOddDer d) (c : K) (a : Finset ι → ExteriorAlgebra K V) :
    Dtot d (c ^ p • a) = c ^ p • Dtot d a := by
  funext t
  simp only [Dtot, delta, Pi.smul_apply, d_smul_pow p d hd, Finset.smul_sum, smul_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact smul_comm _ _ _
end GlobalTheory.DI.PhiClosed
