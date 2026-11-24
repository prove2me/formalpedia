-- Prove2me | solution 1 for GlobalTheory.T.inducedClassFunctionFromSubgroup_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:41.231535+00:00
-- url     : https://prove2.me/submissions/aaf6eea6-b3ae-4525-843d-492bd2fbc5bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTrans
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Theorems.Thm_GlobalTheory_BrauerZero_ind_ind_of_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] [Finite G] (K A : Subgroup G), K ≤ A → ∀ (ψ : K → ℂ), ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ := by
  first | exact @GlobalTheory.BrauerZero.ind_ind_of_le | exact GlobalTheory.BrauerZero.ind_ind_of_le | (intros; apply GlobalTheory.BrauerZero.ind_ind_of_le <;> assumption)
end _root_.GlobalTheory.T
