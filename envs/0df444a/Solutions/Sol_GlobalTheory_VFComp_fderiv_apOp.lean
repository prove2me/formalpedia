-- Prove2me | solution 1 for GlobalTheory.VFComp.fderiv_apOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:13.064238+00:00
-- url     : https://prove2.me/submissions/97569ce0-0b3a-4a75-bc8c-df2a47877bff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Theorems.Thm_GlobalTheory_VFComp_dw_contDiffOn
import Theorems.Thm_GlobalTheory_VFComp_diffAt_of

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
theorem _root_.solution {U : Set (E d)} (hU : IsOpen U) (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (ha : ∀ n w, ContDiffOn ℝ ∞ (a n w) U) {u : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) {x : E d} (hx : x ∈ U)
    (j : Fin d) :
    fderiv ℝ (apOp m a u) x (ev j) = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      (fderiv ℝ (a n w) x (ev j) * dw (List.ofFn w) u x + a n w x * dw (j :: List.ofFn w) u x) := by
  have hd := HasFDerivAt.sum (u := Finset.range (m + 1)) (x := x)
    (A := fun n => ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u) fun n _ =>
      HasFDerivAt.sum (u := Finset.univ) fun w _ =>
        (diffAt_of hU (ha n w) hx).hasFDerivAt.mul
          (diffAt_of hU (dw_contDiffOn hU hu (List.ofFn w)) hx).hasFDerivAt
  have he : apOp m a u = ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d, a n w * dw (List.ofFn w) u := by
    funext y
    simp [apOp, Finset.sum_apply]
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [dw]
  ring
end GlobalTheory.VFComp
