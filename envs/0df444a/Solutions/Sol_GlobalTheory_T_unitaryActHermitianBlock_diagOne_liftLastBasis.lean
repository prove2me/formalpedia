-- Prove2me | solution 1 for GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:58.008063+00:00
-- url     : https://prove2.me/submissions/9ff6a2d6-44c1-4cd0-9c52-646367b41f19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActHermitianBlockDiagOneLiftLastBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActHermitianBlockDiagOneLiftLastBasisStatement
import Theorems.Thm_GlobalTheory_JR_Step_actU_uEmb_liftH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by
  first | exact @GlobalTheory.JR.Step.actU_uEmb_liftH | exact GlobalTheory.JR.Step.actU_uEmb_liftH | (intros; apply GlobalTheory.JR.Step.actU_uEmb_liftH <;> assumption)
end _root_.GlobalTheory.T
