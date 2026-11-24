-- Prove2me | solution 1 for GlobalTheory.HCA.eqOn_dw_lincomb_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:34.848914+00:00
-- url     : https://prove2.me/submissions/6544e5fc-98de-4482-927e-012f0043e01f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
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
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d))
    (u v : E d → ℂ) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) (s t : ℂ) :
    Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U := by
  induction w with
  | nil => intro x _; rfl
  | cons j w ih =>
    intro x hx
    have hn := hU.mem_nhds hx
    have he : dw w (s • u + t • v) =ᶠ[nhds x] s • dw w u + t • dw w v := ih.eventuallyEq_of_mem hn
    have hdu : DifferentiableAt ℝ (dw w u) x :=
      ((contDiffOn_dw_of_isOpen hU w u hu).contDiffAt hn).differentiableAt (by simp)
    have hdv : DifferentiableAt ℝ (dw w v) x :=
      ((contDiffOn_dw_of_isOpen hU w v hv).contDiffAt hn).differentiableAt (by simp)
    have hd : HasFDerivAt (s • dw w u + t • dw w v)
        (s • fderiv ℝ (dw w u) x + t • fderiv ℝ (dw w v) x) x :=
      (hdu.hasFDerivAt.const_smul s).add (hdv.hasFDerivAt.const_smul t)
    show fderiv ℝ (dw w (s • u + t • v)) x (ev j)
      = s • fderiv ℝ (dw w u) x (ev j) + t • fderiv ℝ (dw w v) x (ev j)
    rw [he.fderiv_eq, hd.fderiv]
    rfl
end GlobalTheory.HCA
