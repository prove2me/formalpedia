-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_leftMulMatrix_of_commute_companion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:10.995189+00:00
-- url     : https://prove2.me/submissions/face228e-20ce-4962-9743-f8a85e36e659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitLeftMulMatrixOfCommuteCompanion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitLeftMulMatrixOfCommuteCompanionStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_centr


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  first | exact @GlobalTheory.JR.LinDesc.centr | exact GlobalTheory.JR.LinDesc.centr | (intros; apply GlobalTheory.JR.LinDesc.centr <;> assumption)
end _root_.GlobalTheory.T
