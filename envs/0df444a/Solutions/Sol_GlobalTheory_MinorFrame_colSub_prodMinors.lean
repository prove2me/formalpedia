-- Prove2me | solution 1 for GlobalTheory.MinorFrame.colSub_prodMinors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:19:52.766797+00:00
-- url     : https://prove2.me/submissions/2c35784b-3253-4112-a0d2-687ee2e177c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Theorems.Thm_GlobalTheory_MinorFrame_colSub_minorAt
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
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {a d : ℕ} {n : ι → ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (T : Tup ι a d n) :
    colSub g (prodMinors T) = detChar n g • prodMinors T := by
  unfold prodMinors detChar
  simp only [map_prod, colSub_minorAt, smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_prod, map_pow]
end GlobalTheory.MinorFrame
