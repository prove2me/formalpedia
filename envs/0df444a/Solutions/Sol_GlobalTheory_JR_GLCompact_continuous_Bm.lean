-- Prove2me | solution 1 for GlobalTheory.JR.GLCompact.continuous_Bm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:36.00924+00:00
-- url     : https://prove2.me/submissions/64dffe02-223e-4b45-b223-2ff6e5a6634e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportJacquetRallisOrbitalIntegrand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLCompact
namespace GlobalTheory.JR.GLCompact
theorem _root_.solution {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Bm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((continuous_fst.pow (j : ℕ)).matrix_mulVec (continuous_fst.comp continuous_snd))
end GlobalTheory.JR.GLCompact
