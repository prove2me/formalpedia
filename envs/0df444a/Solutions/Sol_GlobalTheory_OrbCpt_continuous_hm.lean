-- Prove2me | solution 1 for GlobalTheory.OrbCpt.continuous_hm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:41.765851+00:00
-- url     : https://prove2.me/submissions/fe3c5702-0110-441c-9bf2-f46ba8b16947

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer
import Theorems.Thm_GlobalTheory_OrbCpt_continuous_gsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology Polynomial
noncomputable section
open GlobalTheory GlobalTheory.OrbCpt
variable {k : Type} [NontriviallyNormedField k] {r : ℕ}
namespace GlobalTheory.OrbCpt
theorem _root_.solution (p : k[X]) :
    Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => hm p q.1 q.2 := by
  unfold hm
  exact continuous_finsetSum _ fun m _ =>
    (continuous_const_smul (p.coeff m)).comp (continuous_gsum m)
end GlobalTheory.OrbCpt
