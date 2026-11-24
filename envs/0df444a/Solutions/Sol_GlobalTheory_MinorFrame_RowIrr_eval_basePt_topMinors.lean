-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RowIrr.eval_basePt_topMinors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:20:52.50774+00:00
-- url     : https://prove2.me/submissions/798f3301-8515-446c-a28e-422f0f593652

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EvalBasePtTopMinors
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
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RowIrr
open GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame.RowIrr
theorem _root_.solution {a d : ℕ} (h : a ≤ d) (n : ι → ℕ) : eval (basePt ι d a) (topMinors h n) = 1 := by
  simp only [topMinors, prodMinors, minorAt, map_prod, RingHom.map_det]
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => ?_
  have : (RingHom.mapMatrix (eval (basePt ι d a)))
      (Matrix.of fun i i' : Fin a => (X (τ, (topRows h).1 i, i') : Pol ι d a)) = 1 := by
    ext i i'
    simp [basePt, topRows, Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]
end GlobalTheory.MinorFrame.RowIrr
