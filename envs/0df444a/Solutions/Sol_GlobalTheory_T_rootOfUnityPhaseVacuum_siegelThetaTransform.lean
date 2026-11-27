-- Prove2me | solution 1 for GlobalTheory.T.rootOfUnityPhaseVacuum_siegelThetaTransform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:35.686405+00:00
-- url     : https://prove2.me/submissions/e7a7285d-d22b-4808-ab94-d46d90ab208f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RootOfUnityPhaseVacuumSiegelThetaTransform
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RootOfUnityPhaseVacuumSiegelThetaTransformStatement
import Theorems.Thm_GlobalTheory_Phase_WeilPV_pv_of_transS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  first | exact @GlobalTheory.Phase.WeilPV.pv_of_transS | exact GlobalTheory.Phase.WeilPV.pv_of_transS | (intros; apply GlobalTheory.Phase.WeilPV.pv_of_transS <;> assumption)
end _root_.GlobalTheory.T
