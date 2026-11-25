-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.trace_pow_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:04:10.124867+00:00
-- url     : https://prove2.me/submissions/e1e45300-5236-4564-8b34-46e74542afc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_rowE_X
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_glRel_rowE
import Theorems.Thm_GlobalTheory_Mem_GelfCheck_trace_pow_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
namespace GlobalTheory.Mem.GelfCheck
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (t : Fin n) (k : ℕ) :
    (rowE R (r+1) n ^ k).trace (X (0, t)) = gelfC (Pi.single (0 : Fin (r+1)) (1 : R)) k • X (0, t) := by
  refine trace_pow_apply (glRel_rowE R (r+1) n) (fun a => ?_) (fun a b hab => ?_) k
  · rw [rowE_X]; split_ifs with h <;> simp [h]
  · rw [rowE_X, if_neg (ne_of_gt (lt_of_le_of_lt (Fin.zero_le a) hab))]
end GlobalTheory.Mem.GelfCheck
