-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstantCompactSupport_jacquetRallisDescent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:39.452135+00:00
-- url     : https://prove2.me/submissions/3d385bc4-024a-4063-bae5-9192cd64c984

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportJacquetRallisDesc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportJacquetRallisDescStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_desc_isTest


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → IsTest (LinDesc.desc A M hG lam α f') := by
  first | exact @GlobalTheory.JR.LinDesc.desc_isTest | exact GlobalTheory.JR.LinDesc.desc_isTest | (intros; apply GlobalTheory.JR.LinDesc.desc_isTest <;> assumption)
end _root_.GlobalTheory.T
