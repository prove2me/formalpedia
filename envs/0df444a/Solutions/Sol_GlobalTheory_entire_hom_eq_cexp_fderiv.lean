-- Prove2me | solution 1 for GlobalTheory.entire_hom_eq_cexp_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:37.384878+00:00
-- url     : https://prove2.me/submissions/17611082-48b6-4ef2-8051-e884b6c6bdfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AutomorphyFactorExpLinearOfCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (h : V → ℂ) (hd : Differentiable ℂ h) (h0 : h 0 = 1) (hadd : ∀ y z, h (y + z) = h y * h z)
    (z : V) : h z = cexp (fderiv ℂ h 0 z) := by
  set B : V →L[ℂ] ℂ := fderiv ℂ h 0 with hB
  have hder : ∀ w, HasFDerivAt h (h w • B) w := by
    intro w
    have e : h = fun u => h w * h (u - w) := by
      funext u
      rw [← hadd]; congr 1; abel
    have h1 : HasFDerivAt h B (w - w) := by
      rw [sub_self]; exact (hd 0).hasFDerivAt
    have h2 : HasFDerivAt (fun u => h (u - w)) B w := by
      have := HasFDerivAt.comp (f := fun u => u - w) w h1 ((hasFDerivAt_id w).sub_const w)
      simpa [Function.comp_def] using this
    have h3 := h2.const_mul (h w)
    rw [← e] at h3
    exact h3
  have hφ : ∀ w, HasFDerivAt (fun u => h u * cexp (-(B u))) (0 : V →L[ℂ] ℂ) w := by
    intro w
    have h1 : HasFDerivAt (fun u => cexp (-(B u))) (cexp (-(B w)) • (-B)) w :=
      (B.hasFDerivAt.neg).cexp
    have h2 := (hder w).mul h1
    have e : h w • cexp (-B w) • -B + cexp (-B w) • h w • B = 0 := by
      rw [smul_comm (h w) (cexp (-B w)), smul_neg, smul_neg, neg_add_cancel]
    rw [e] at h2
    exact h2
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun u => h u * cexp (-(B u)))
    (fun w => (hφ w).differentiableAt) (fun w => (hφ w).fderiv) z 0
  simp only [h0, map_zero, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  have := Complex.exp_ne_zero (B z)
  field_simp at hc
  exact hc
end GlobalTheory
