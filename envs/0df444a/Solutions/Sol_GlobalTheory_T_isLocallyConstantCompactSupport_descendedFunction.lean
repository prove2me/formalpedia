-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:35.535528+00:00
-- url     : https://prove2.me/submissions/5493a3fc-445c-42a4-8442-9caae7821309

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportDescendedFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportDescendedFunctionStatement
import Theorems.Thm_GlobalTheory_JR_descFn_isTest


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  first | exact @GlobalTheory.JR.descFn_isTest | exact GlobalTheory.JR.descFn_isTest | (intros; apply GlobalTheory.JR.descFn_isTest <;> assumption)
end _root_.GlobalTheory.T
