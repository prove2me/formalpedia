-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.gauss_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:14.647142+00:00
-- url     : https://prove2.me/submissions/5b1197a4-d58a-498d-9a42-813864f8db1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Theorems.Thm_GlobalTheory_HeckeTheta_hmon_zero
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
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
open GlobalTheory GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta
theorem _root_.solution {n : I → ℤ} (hn : ∃ i, n i ≠ 0) : gauss n 0 = 0 := by
  obtain ⟨i, hi⟩ := hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hmon_zero hi])
end GlobalTheory.HeckeTheta
