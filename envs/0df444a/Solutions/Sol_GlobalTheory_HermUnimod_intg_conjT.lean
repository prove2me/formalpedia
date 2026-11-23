-- Prove2me | solution 1 for GlobalTheory.HermUnimod.intg_conjT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:19.344641+00:00
-- url     : https://prove2.me/submissions/fa070a48-12ea-4feb-a59f-3a9b6a55448f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n m : Type} {A : Matrix n m E} (hA : Intg A) :
    Intg Aᴴ := by
  intro i j
  rw [conjTranspose_apply, hs]
  exact hA j i
end GlobalTheory.HermUnimod
