-- Prove2me | solution 1 for GlobalTheory.OrbCpt.continuous_gsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:24.014398+00:00
-- url     : https://prove2.me/submissions/9d54748b-50bb-40fc-88fb-226800fca324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompactPreimageNormCentralizerHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjugatesSeparableMatrixCompactModCentralizer

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
theorem _root_.solution (m : ℕ) :
    Continuous fun q : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin r) k => gsum q.1 q.2 m := by
  induction m with
  | zero => simpa [gsum] using continuous_const
  | succ m ih => simp only [gsum]; fun_prop
end GlobalTheory.OrbCpt
