-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.lin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:07.810334+00:00
-- url     : https://prove2.me/submissions/0719a7fc-299f-4c9f-a914-1e32d5291444

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
theorem _root_.solution {ι : Type} [Fintype ι] (t : ι → ℝ) (z : ι → ℂ) :
    lin t z = 2 * (Real.pi : ℂ) * ∑ i, z i * t i := by
  simp [lin, mul_comm]
end GlobalTheory.CompanionTheory.EisTube
