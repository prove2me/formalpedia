-- Prove2me | solution 1 for GlobalTheory.map_maximalIdeal_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:51.35761+00:00
-- url     : https://prove2.me/submissions/fe589234-8099-43e0-959c-351340f1adaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring

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
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution {S O : Type*} [CommRing S] [IsLocalRing S] [CommRing O]
    [IsLocalRing O] (φ : S →+* O) [IsLocalHom φ] (n : ℕ) :
    (maximalIdeal S ^ n).map φ ≤ maximalIdeal O ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le φ) n
end GlobalTheory
