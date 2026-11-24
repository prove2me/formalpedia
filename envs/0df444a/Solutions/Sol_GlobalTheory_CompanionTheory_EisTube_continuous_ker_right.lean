-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.continuous_ker_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:23.819624+00:00
-- url     : https://prove2.me/submissions/ea82b3da-c47c-4142-bfc6-1074b0fab2c0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] (z : ι → ℂ) : Continuous (ker z) := by
  unfold ker
  fun_prop
end GlobalTheory.CompanionTheory.EisTube
