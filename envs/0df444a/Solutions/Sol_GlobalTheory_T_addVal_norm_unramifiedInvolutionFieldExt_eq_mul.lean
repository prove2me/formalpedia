-- Prove2me | solution 1 for GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:01.415175+00:00
-- url     : https://prove2.me/submissions/39baf1e1-8926-484d-840e-11c9a2c6bd03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMulStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormVal_normval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormVal.normval | exact GlobalTheory.UnitLemma.Unr.NormVal.normval | (intros; apply GlobalTheory.UnitLemma.Unr.NormVal.normval <;> assumption)
end _root_.GlobalTheory.T
