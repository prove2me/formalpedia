-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallisTransferFactor_glBorderedConjugationAction_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:46.217254+00:00
-- url     : https://prove2.me/submissions/19ff3afd-fb4c-49f5-9696-057feee15f1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorGlBorderedConjugation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorGlBorderedConjugationStatement
import Theorems.Thm_GlobalTheory_JR_omega_act_glO


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
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y := by
  first | exact @GlobalTheory.JR.omega_act_glO | exact GlobalTheory.JR.omega_act_glO | (intros; apply GlobalTheory.JR.omega_act_glO <;> assumption)
end _root_.GlobalTheory.T
