-- Prove2me | solution 1 for GlobalTheory.HCA.SupEst.tr_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:41.238475+00:00
-- url     : https://prove2.me/submissions/5817ea5b-2527-4cf4-8c13-891490e7277e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup
import Theorems.Thm_GlobalTheory_HCA_SupEst_dw_zero_fun
import Theorems.Thm_GlobalTheory_HCA_eqOn_dw_of_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SupEst
variable {d : ℕ}
namespace GlobalTheory.HCA.SupEst
theorem _root_.solution {ι : Type} (P : Sys d ι) (i : ι) {φ : E d → ℂ} {x : E d}
    (hx : x ∉ tsupport φ) : P.tr i φ x = 0 := by
  unfold Sys.tr trOp
  refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun w _ => ?_
  have hO : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  have hEq : Set.EqOn (fun y => P.a i n w y * φ y) (fun _ => (0 : ℂ)) (tsupport φ)ᶜ := by
    intro y hy
    have : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have := eqOn_dw_of_isOpen hO (List.ofFn w) _ _ hEq hx
  rw [this, dw_zero_fun]
  simp
end GlobalTheory.HCA.SupEst
