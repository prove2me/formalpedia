-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.continuous_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:24.707921+00:00
-- url     : https://prove2.me/submissions/d389b085-9544-42c8-8cf0-204f7c13d27e

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
theorem _root_.solution {ι : Type} [Fintype ι] : Continuous (lin (ι := ι)) := by
  unfold lin
  fun_prop
end GlobalTheory.CompanionTheory.EisTube
