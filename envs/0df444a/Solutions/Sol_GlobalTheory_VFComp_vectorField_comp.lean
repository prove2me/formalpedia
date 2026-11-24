-- Prove2me | solution 1 for GlobalTheory.VFComp.vectorField_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:31.262484+00:00
-- url     : https://prove2.me/submissions/2d002b76-68f8-46a4-add9-0aa8c3f9fdf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Theorems.Thm_GlobalTheory_VFComp_coefVF_contDiffOn
import Theorems.Thm_GlobalTheory_VFComp_symb_coefVF
import Theorems.Thm_GlobalTheory_VFComp_apOp_coefVF

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
namespace GlobalTheory.VFComp
theorem _root_.solution : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (c : Fin d → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ j, ContDiffOn ℝ ∞ (c j) U) → ∃ a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) ∧ (∀ x ξ : E d, symb (m + 1) a' x ξ = (∑ j, c j x * ((ξ j : ℝ) : ℂ)) * symb m a x ξ) ∧ ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ∀ x ∈ U, ∑ j, c j x * fderiv ℝ (apOp m a u) x (ev j) = apOp (m + 1) a' u x := by
  intro d m U hU a c ha hc
  exact ⟨GlobalTheory.VFComp.coefVF m a c, GlobalTheory.VFComp.coefVF_contDiffOn hU m a c ha hc,
    GlobalTheory.VFComp.symb_coefVF m a c, fun u hu x hx => GlobalTheory.VFComp.apOp_coefVF hU m a c ha hu hx⟩
end GlobalTheory.VFComp
