-- Prove2me | solution 1 for GlobalTheory.MinorFrame.eval_detG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:21.589658+00:00
-- url     : https://prove2.me/submissions/c3b6e575-2e70-4e3f-a9d4-a07ba1ee24a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type}
namespace GlobalTheory.MinorFrame
theorem _root_.solution [Fintype ι] (a : ℕ) (n : ι → ℕ) (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    eval (fun v : ι × Fin a × Fin a => g v.1 v.2.1 v.2.2) (detG a n) = detChar n g := by
  unfold detG detChar
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext i j
  simp
end GlobalTheory.MinorFrame
