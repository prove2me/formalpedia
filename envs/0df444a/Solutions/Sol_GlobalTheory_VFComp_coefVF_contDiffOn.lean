-- Prove2me | solution 1 for GlobalTheory.VFComp.coefVF_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:23.838308+00:00
-- url     : https://prove2.me/submissions/ba84f6a4-7f60-4b72-9a0e-50d9f62ea14f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Theorems.Thm_GlobalTheory_VFComp_dw_contDiffOn

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
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) (m : ℕ)
    (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) (hc : ∀ j, ContDiffOn ℝ ∞ (c j) U) (n : ℕ) (w : Fin n → Fin d) :
    ContDiffOn ℝ ∞ (coefVF m a c n w) U := by
  have hB : ContDiffOn ℝ ∞ (coefB m a c n w) U := by
    unfold coefB
    split_ifs
    · exact ContDiffOn.sum fun j _ => (hc j).mul (dw_contDiffOn hU (ha n w) [j])
    · exact contDiffOn_const
  have hA : ContDiffOn ℝ ∞ (coefA m a c n w) U := by
    cases n with
    | zero => exact contDiffOn_const
    | succ k =>
      show ContDiffOn ℝ ∞ (fun x => if k ≤ m then c (w 0) x * a k (Fin.tail w) x else 0) U
      split_ifs
      · exact (hc _).mul (ha _ _)
      · exact contDiffOn_const
  exact hA.add hB
end GlobalTheory.VFComp
