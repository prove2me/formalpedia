-- Prove2me | solution 1 for GlobalTheory.AnArc.orth_ker_iff_forall_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:11:05.863912+00:00
-- url     : https://prove2.me/submissions/e8418681-534a-40a2-a579-bb475e477d11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Theorems.Thm_GlobalTheory_AnArc_orth_ker_iff
import Theorems.Thm_GlobalTheory_AnArc_l_eq_zero_of_forall_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (v : A.La) :
    (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ ∀ s : ℂ, (s • A.P0 v).2 ∈ A.abelian₂ := by
  rw [orth_ker_iff]
  refine and_congr_right fun hv => ⟨fun hl s => ?_, A.l_eq_zero_of_forall_smul_mem hv⟩
  simp [hv, hl]
end GlobalTheory.AnArc
