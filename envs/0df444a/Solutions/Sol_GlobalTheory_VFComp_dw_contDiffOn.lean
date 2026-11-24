-- Prove2me | solution 1 for GlobalTheory.VFComp.dw_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:09.020793+00:00
-- url     : https://prove2.me/submissions/458e5d9c-dc28-4a4f-aae8-8541d8353c72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn

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
open GlobalTheory GlobalTheory.VFComp
variable {d : ℕ}
namespace GlobalTheory.VFComp
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) :
    ∀ w : List (Fin d), ContDiffOn ℝ ∞ (dw w u) U
  | [] => hu
  | j :: w => by
    have h := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 (solution hU hu w)).2
    exact h.clm_apply contDiffOn_const
end GlobalTheory.VFComp
