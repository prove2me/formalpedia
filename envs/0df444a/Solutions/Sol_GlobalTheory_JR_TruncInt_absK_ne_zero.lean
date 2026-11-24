-- Prove2me | solution 1 for GlobalTheory.JR.TruncInt.absK_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:34.878299+00:00
-- url     : https://prove2.me/submissions/1a015f62-ca4e-4e3a-8618-4b6a6f7c856d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegral

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TruncInt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.TruncInt
theorem _root_.solution (A : Et F E) {t : A.K} (h : IsUnit t) : A.absK t ≠ 0 := by
  unfold Et.absK
  rw [dif_pos h]
  exact NNReal.coe_ne_zero.2 (IsUnit.map (distribHaarChar A.K) (Group.isUnit h.unit)).ne_zero
end GlobalTheory.JR.TruncInt
