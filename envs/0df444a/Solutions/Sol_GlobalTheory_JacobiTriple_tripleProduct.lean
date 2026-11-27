-- Prove2me | solution 1 for GlobalTheory.JacobiTriple.tripleProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:53:26.145259+00:00
-- url     : https://prove2.me/submissions/8637f4bf-793b-4d84-b5d3-003e9c732588

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductLimitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleProductTwoVariableTheta
import Theorems.Thm_GlobalTheory_JacobiTriple_multipliable_tpFactor
import Theorems.Thm_GlobalTheory_JacobiTriple_norm_exp_pi_I_lt_one
import Theorems.Thm_GlobalTheory_JacobiTriple_qPoch_tendsto
import Theorems.Thm_GlobalTheory_JacobiTriple_tpFactor_eq
import Theorems.Thm_GlobalTheory_T_jacobiTriple_finite_product
import Theorems.Thm_GlobalTheory_T_jacobi_triple_product_limit
import Theorems.Thm_P2M_GlobalTheory_JacobiTriple_jacobiTheta__term_eq_zpow_0d4763adc8fd


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
noncomputable section
open GlobalTheory GlobalTheory.JacobiTriple
namespace GlobalTheory.JacobiTriple
theorem _root_.solution : GlobalTheory.ThetaWeberRoad.TripleProduct := by
  intro τ z
  set s := cexp (π * I * (τ : ℂ)) with hs
  set x := cexp (2 * π * I * z) with hx
  have hτ : 0 < (τ : ℂ).im := τ.2
  have hs1 : ‖s‖ < 1 := norm_exp_pi_I_lt_one (τ : ℂ) hτ
  have hs0 : s ≠ 0 := exp_ne_zero _
  have hx0 : x ≠ 0 := exp_ne_zero _
  have ht1 : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  obtain ⟨hP, hP0, -⟩ := qPoch_tendsto (s ^ 2) ht1
  have hT := GlobalTheory.T.jacobi_triple_product_limit (τ : ℂ) z hτ
  rw [(multipliable_tpFactor τ z).hasProd_iff_tendsto_nat]
  have key : ∀ n : ℕ, ∏ k ∈ Finset.range n, GlobalTheory.ThetaWeberRoad.tpFactor τ z k =
      qPoch (s ^ 2) n * ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
        finCoeff (cexp (π * I * (τ : ℂ)) ^ 2) n j * jacobiTheta₂_term j z τ := by
    intro n
    rw [Finset.prod_congr rfl (fun k _ => tpFactor_eq τ z k), Finset.prod_mul_distrib]
    have hf := GlobalTheory.T.jacobiTriple_finite_product s x hs0 hs1 hx0 n
    simp only [hs, hx] at hf
    simp only [hf, jacobiTheta₂_term_eq_zpow]
    rfl
  simp_rw [key]
  have := hP.mul hT
  rwa [mul_left_comm, mul_inv_cancel₀ hP0, mul_one] at this
end GlobalTheory.JacobiTriple
