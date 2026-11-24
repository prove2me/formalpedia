-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.val_pow_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:53.270078+00:00
-- url     : https://prove2.me/submissions/4b20c432-152c-496f-8d11-9f9c48394603

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTraceGramBlockMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOdd
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_mul_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {K : UQ} {a : K.E} (ha : a ≠ 0) (n : ℕ) : val K.O (a ^ n) = n * val K.O a := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_of_ne (pow_ne_zero _ ha) ha, ih]; push_cast; ring
end GlobalTheory.UnitLemma.Unr
