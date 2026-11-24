-- Prove2me | solution 1 for GlobalTheory.MinorFrame.colSub_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:19.484813+00:00
-- url     : https://prove2.me/submissions/e16d3134-3a0d-4cec-bb91-e300278458ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
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
open Classical MeasureTheory
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {d a : ℕ} (A B : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub (fun τ => A τ * B τ) P = colSub A (colSub B P) := by
  have : (colSub (fun τ => A τ * B τ) : Pol ι d a →ₐ[ℂ] Pol ι d a) = (colSub A).comp (colSub B) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.mul_sum, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) this
end GlobalTheory.MinorFrame
