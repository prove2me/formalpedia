-- Prove2me | solution 1 for GlobalTheory.HCA.dw_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:33.856108+00:00
-- url     : https://prove2.me/submissions/e9b2a3a1-36ba-4187-b4b3-107d38034fb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow

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
theorem _root_.solution {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (a b : Fin d) {g : E d → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : Set.EqOn (dw [a, b] g) (dw [b, a] g) U := by
  intro x hx
  have hx' := hU.mem_nhds hx
  have hga : ContDiffAt ℝ ∞ g x := hg.contDiffAt hx'
  have hsym := hga.isSymmSndFDerivAt (by simpa using (WithTop.coe_le_coe.2 le_top : (2 : WithTop ℕ∞) ≤ ∞))
  have hd1 : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ g) x := by
    have := (contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg
    exact (this.2.contDiffAt hx').differentiableAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ g y (ev b)) x (ev a) = fderiv ℝ (fun y => fderiv ℝ g y (ev a)) x (ev b)
  rw [fderiv_clm_apply hdf (differentiableAt_const _), fderiv_clm_apply hdf (differentiableAt_const _)]
  have h0 : ∀ c : E d, fderiv ℝ (fun _ : E d => c) x = 0 := fun c => fderiv_const_apply c
  simp only [h0, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hsym _ _
end GlobalTheory.HCA
