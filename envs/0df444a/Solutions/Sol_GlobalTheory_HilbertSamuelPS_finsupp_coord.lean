-- Prove2me | solution 1 for GlobalTheory.HilbertSamuelPS.finsupp_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:30:45.022289+00:00
-- url     : https://prove2.me/submissions/659040fb-fae9-4ac3-b57b-1d4cd8164195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.HilbertSamuelPS
open MvPowerSeries
namespace GlobalTheory.HilbertSamuelPS
theorem _root_.solution {D : ℕ} (e : Fin D →₀ ℕ) (a : Fin D → ℕ) (m : ℕ) (d : Fin D) :
    (m • e + ∑ d', Finsupp.single d' (a d')) d = m * e d + a d := by
  simp [Finsupp.single_apply]
end GlobalTheory.HilbertSamuelPS
