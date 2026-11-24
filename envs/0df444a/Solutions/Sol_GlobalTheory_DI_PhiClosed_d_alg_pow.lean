-- Prove2me | solution 1 for GlobalTheory.DI.PhiClosed.d_alg_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:30.93749+00:00
-- url     : https://prove2.me/submissions/39ae8652-ab48-4c81-a0b4-9bd4d12a8df7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobeniusSplittingClosed

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
theorem _root_.solution (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) (c : K) (n : ℕ) :
    d (algebraMap K (ExteriorAlgebra K V) c ^ (n + 1)) =
      (n + 1) • (algebraMap K (ExteriorAlgebra K V) c ^ n * d (algebraMap K (ExteriorAlgebra K V) c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' _ (n + 1), hd.mul, ih, AlgHom.commutes]
    have hc : d (algebraMap K (ExteriorAlgebra K V) c) * algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) =
        algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) * d (algebraMap K (ExteriorAlgebra K V) c) := by
      rw [← map_pow]
      exact (Algebra.commutes _ _).symm
    rw [hc, mul_smul_comm, ← mul_assoc, ← pow_succ', succ_nsmul' _ (n + 1)]
end GlobalTheory.DI.PhiClosed
