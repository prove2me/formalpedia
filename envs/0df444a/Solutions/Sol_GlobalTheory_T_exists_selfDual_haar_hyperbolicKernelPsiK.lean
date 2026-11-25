-- Prove2me | solution 1 for GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:44.181902+00:00
-- url     : https://prove2.me/submissions/d870c091-bd07-4065-95d4-16cb8b17e737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualHaarHyperbolicKernelPsiK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualHaarHyperbolicKernelPsiKStatement
import Theorems.Thm_GlobalTheory_JR_Hyp_selfDual_kx_exists


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  first | exact @GlobalTheory.JR.Hyp.selfDual_kx_exists | exact GlobalTheory.JR.Hyp.selfDual_kx_exists | (intros; apply GlobalTheory.JR.Hyp.selfDual_kx_exists <;> assumption)
end _root_.GlobalTheory.T
