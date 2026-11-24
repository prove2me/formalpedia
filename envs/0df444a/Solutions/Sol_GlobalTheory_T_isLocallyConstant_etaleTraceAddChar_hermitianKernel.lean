-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:10.121509+00:00
-- url     : https://prove2.me/submissions/05612bf1-c525-42d6-9fad-aad5f98f5f1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_isLocallyConstant_psiK_kerL


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  first | exact @GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | exact GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | (intros; apply GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL <;> assumption)
end _root_.GlobalTheory.T
