-- Prove2me | solution 1 for GlobalTheory.SliceTaylor.norm_le_norm_elim_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:10.834634+00:00
-- url     : https://prove2.me/submissions/b0d2bd94-3494-49b5-823e-d3ff1e443422

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivPdLe
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceTaylor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.SliceTaylor
theorem _root_.solution {κ κ' : Type} [Fintype κ] [Fintype κ'] (x h : κ → V) (y : κ' → V) (s : ℝ) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V) + s • padL h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm ((Sum.elim x y : κ ⊕ κ' → V) + s • padL h) (Sum.inr j)
  simp only [Pi.add_apply, Pi.smul_apply, padL, Sum.elim_inr, Pi.zero_apply, smul_zero, add_zero] at this
  exact this
end GlobalTheory.SliceTaylor
