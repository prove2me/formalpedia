-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.absK_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:04.696326+00:00
-- url     : https://prove2.me/submissions/a75b72a1-4e59-481a-97f9-6bb1154c9366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilTorusMulUnipotentCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGaussStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralSqEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralTransformWeilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepresentationQuadraticFieldExists
import Theorems.Thm_GlobalTheory_JR_WeilQuad_absK_unit
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution (A : Et F E) (a : A.Kˣ) : (A.absK a : ℂ) ≠ 0 := by
  rw [absK_unit]; exact_mod_cast (distribHaarChar_pos (A := A.K) (g := a)).ne'
end GlobalTheory.JR.WeilQuad
