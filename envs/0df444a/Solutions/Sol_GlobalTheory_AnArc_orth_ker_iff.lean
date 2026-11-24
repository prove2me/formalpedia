-- Prove2me | solution 1 for GlobalTheory.AnArc.orth_ker_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:32:18.786007+00:00
-- url     : https://prove2.me/submissions/a41ea66f-77d4-4d52-a9d1-d62e6bece26b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
import Theorems.Thm_GlobalTheory_AnArc_EF_apply


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
theorem _root_.solution (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ v.y = 0 ∧ v.l = 0 := by
  constructor
  · intro h
    refine ⟨(Module.forall_dual_apply_eq_zero_iff ℤ _).1 fun φ => ?_, A.Ef_bij.1 (LinearMap.ext fun l => ?_)⟩
    · simpa [EF_apply] using h (La.mk 0 φ.toAddMonoidHom 0) rfl
    · simpa [EF_apply] using h (La.mk 0 0 l) rfl
  · rintro ⟨hy, hl⟩ v' hv'
    simp [EF_apply, hy, hl, hv']
end GlobalTheory.AnArc
