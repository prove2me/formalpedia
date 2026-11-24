-- Prove2me | solution 1 for GlobalTheory.HCA.dw_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:25.25381+00:00
-- url     : https://prove2.me/submissions/037b2416-505c-463a-862e-aeddb5159c2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
import Theorems.Thm_GlobalTheory_HCA_dw_append
import Theorems.Thm_GlobalTheory_HCA_dw_swap
import Theorems.Thm_GlobalTheory_HCA_contDiffOn_dw_of_isOpen


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
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U) {w₁ w₂ : List (Fin d)} (h : w₁.Perm w₂) :
    ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → Set.EqOn (dw w₁ u) (dw w₂ u) U := by
  induction h with
  | nil => intro u _; exact fun _ _ => rfl
  | cons j _ ih =>
    intro u hu z hz
    show fderiv ℝ _ z (ev j) = fderiv ℝ _ z (ev j)
    rw [((ih u hu).eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]
  | swap x y l =>
    intro u hu
    have e1 := dw_append [y, x] l u
    have e2 := dw_append [x, y] l u
    simp only [List.cons_append, List.nil_append] at e1 e2
    rw [e1, e2]
    exact dw_swap hU y x (contDiffOn_dw_of_isOpen hU l u hu)
  | trans _ _ ih₁ ih₂ => intro u hu; exact (ih₁ u hu).trans (ih₂ u hu)
end GlobalTheory.HCA
