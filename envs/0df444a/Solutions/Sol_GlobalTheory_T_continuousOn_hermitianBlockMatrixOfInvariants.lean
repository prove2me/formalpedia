-- Prove2me | solution 1 for GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:22.964331+00:00
-- url     : https://prove2.me/submissions/f9bbe2df-ecbd-4eba-b777-00cd75f1b5d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariantsStatement
import Theorems.Thm_GlobalTheory_JR_ImgSec_continuousOn_mkX_of_isUnit_det


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  first | exact @GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | exact GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | (intros; apply GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det <;> assumption)
end _root_.GlobalTheory.T
