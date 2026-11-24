-- Prove2me | solution 1 for GlobalTheory.HeckeMellin.term_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:57:26.157042+00:00
-- url     : https://prove2.me/submissions/9b5b1057-9d15-4028-ac69-8db4e4012047

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckeTheta_gauss_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckeMellin
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeMellin
theorem _root_.solution {n : I → ℤ} (hn : ∃ i, n i ≠ 0) (s : ℂ) (y : I → ℝ) : term n s 0 y = 0 := by
  have : GlobalTheory.HeckeTheta.dil y (0 : I → ℂ) = 0 := by
    funext i; simp [GlobalTheory.HeckeTheta.dil]
  rw [term, this, GlobalTheory.HeckeTheta.gauss_zero hn, zero_mul]
end GlobalTheory.HeckeMellin
