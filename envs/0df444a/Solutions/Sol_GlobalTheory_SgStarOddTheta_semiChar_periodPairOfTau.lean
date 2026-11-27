-- Prove2me | solution 1 for GlobalTheory.SgStarOddTheta.semiChar_periodPairOfTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:39:58.051366+00:00
-- url     : https://prove2.me/submissions/12e1d5eb-a8df-479b-b2ea-96e5a821edb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
import Theorems.Thm_GlobalTheory_SgStarOddTheta_exp_pi_I_int
import Theorems.Thm_GlobalTheory_mem_lattice_periodPairOfTau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open GlobalTheory GlobalTheory.SgStarOddTheta
open Formalism.L2.Th1.F
namespace GlobalTheory.SgStarOddTheta
theorem _root_.solution (τ : UpperHalfPlane) (m k : ℤ) :
    semiChar (GlobalTheory.periodPairOfTau τ) (m * (τ : ℂ) + k) =
      cexp ((Real.pi : ℂ) * I * ((k - m + m * k : ℤ) : ℂ)) := by
  have hpar : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  have hmem : (m * (τ : ℂ) + k) / 2 ∈ (GlobalTheory.periodPairOfTau τ).lattice ↔ Even m ∧ Even k := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨p, q, e⟩
      have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
        push_cast
        linear_combination -2 * e
      have h1 := congrArg Complex.im e1
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
      rw [h1, add_right_inj, Int.cast_inj] at e1
      exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, by push_cast; ring⟩
  rw [exp_pi_I_int, semiChar]
  by_cases h : Even m ∧ Even k
  · rw [if_pos (hmem.2 h), if_pos (hpar.2 h)]
  · rw [if_neg (fun h' => h (hmem.1 h')), if_neg (fun h' => h (hpar.1 h'))]
end GlobalTheory.SgStarOddTheta
