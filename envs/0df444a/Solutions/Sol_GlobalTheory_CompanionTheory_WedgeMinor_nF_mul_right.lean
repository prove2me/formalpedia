-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeMinor.nF_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:53.995831+00:00
-- url     : https://prove2.me/submissions/47993423-7f39-49f9-9fd6-cfc0e2a2e8f9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeMinor
namespace GlobalTheory.CompanionTheory.WedgeMinor
theorem _root_.solution {K ι κ : Type} [NormedField K] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ K) (s : Matrix κ κ K) : nF (A * s) = nF A * ‖s.det‖ := by
  unfold nF
  rw [Real.iSup_mul_of_nonneg (norm_nonneg _)]
  refine iSup_congr fun t => ?_
  have h : (A * s).submatrix t id = A.submatrix t id * s := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, det_mul, norm_mul]
end GlobalTheory.CompanionTheory.WedgeMinor
