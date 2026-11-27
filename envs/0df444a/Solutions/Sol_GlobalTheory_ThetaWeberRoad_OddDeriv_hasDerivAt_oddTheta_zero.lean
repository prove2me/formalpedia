-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.OddDeriv.hasDerivAt_oddTheta_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:40:51.430493+00:00
-- url     : https://prove2.me/submissions/1bc053e5-f831-4398-8014-65b4afa4885c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_continuousAt_tailProd
import Theorems.Thm_P2M_GlobalTheory_ThetaWeberRoad_OddDeriv_jacobiTheta__shift_a65dbbb4eb2e
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_hasDerivAt_mul_of_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv
namespace GlobalTheory.ThetaWeberRoad.OddDeriv
theorem _root_.solution :
    TripleProduct → ∀ τ : UpperHalfPlane,
      HasDerivAt (oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  intro hT τ
  set F : ℂ → ℂ := fun z => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) *
    (1 - cexp (-(2 * π * I * z))) with hFdef
  set R : ℂ → ℂ := fun z => tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
    tailProd τ (cexp (-(2 * π * I * z))) with hRdef
  have hfun : oddTheta τ = fun z => F z * R z := by
    funext z
    simp only [oddTheta, F, R]
    rw [jacobiTheta₂_shift hT]
    ring
  have hF0 : F 0 = 0 := by simp [F]
  have h1 : HasDerivAt (fun z : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)))
      (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1)) 0 :=
    ((((hasDerivAt_id (0 : ℂ)).add_const (1 / 2)).const_mul (π * I)).const_add _).cexp
  have h2 : HasDerivAt (fun z : ℂ => 1 - cexp (-(2 * π * I * z)))
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).neg.cexp).const_sub 1
  have hF : HasDerivAt F (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1) *
      (1 - cexp (-(2 * π * I * 0))) + cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) *
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1)))) 0 := h1.mul h2
  have hR : ContinuousAt R 0 := by
    have hu : Continuous fun z : ℂ => cexp (2 * π * I * z) := by fun_prop
    have hv : Continuous fun z : ℂ => cexp (-(2 * π * I * z)) := by fun_prop
    exact (continuousAt_const.mul ((continuousAt_tailProd τ _).comp hu.continuousAt)).mul
      ((continuousAt_tailProd τ _).comp hv.continuousAt)
  rw [hfun]
  have key := hasDerivAt_mul_of_eq_zero hF hF0 hR
  convert key using 1
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have hq : (Function.Periodic.qParam 24 (τ : ℂ)) ^ 3 = cexp (π * I * (τ : ℂ) / 4) := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hI : cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) = cexp (π * I * (τ : ℂ) / 4) * I := by
    rw [Complex.exp_add]
    congr 1
    rw [show π * I * (0 + 1 / 2) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  simp only [R, mul_zero, neg_zero, Complex.exp_zero, hT1, hI]
  unfold ModularForm.eta
  rw [mul_pow, hq]
  ring_nf
  rw [Complex.I_sq]
  ring
end GlobalTheory.ThetaWeberRoad.OddDeriv
