-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.loc_heat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:17.320024+00:00
-- url     : https://prove2.me/submissions/9df9cd4f-a13a-440d-8fd3-b56baee6ce15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Theorems.Thm_GlobalTheory_SW_HeatTerm_loc_Z
import Theorems.Thm_GlobalTheory_SW_HeatTerm_quad_add
import Theorems.Thm_GlobalTheory_SW_HeatTerm_deriv_deriv_const_mul_cexp_bilinear_at_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (h : (C * Z + D).det ≠ 0) (a b : Fin N) (K : ℂ) :
    2 * Real.pi * I * deriv (fun s : ℂ => K * loc C D (Z + Matrix.single a b s) z z') 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
        K * loc C D Z (z + Matrix.single k a s) (z' + Matrix.single k b t)) 0) 0 := by
  rw [((loc_Z C D Z z z' h a b).const_mul K).deriv]
  have h1 : ∀ (w w' : Matrix (Fin n) (Fin N) ℂ), K * loc C D Z w w' =
      (K * ((C * Z + D).det ^ n)⁻¹) *
        cexp (-(2 * Real.pi * I) * ∑ k, w' k ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ w k) := by
    intro w w'
    rw [loc, mul_inv, ← Complex.exp_neg, neg_mul, ← mul_assoc K]
  simp only [h1, quad_add, deriv_deriv_const_mul_cexp_bilinear_at_zero]
  rw [← h1, ← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  generalize (∑ k, (z' k ᵥ* ((C * Z + D)⁻¹ * C)) a * (((C * Z + D)⁻¹ * C) *ᵥ z k) b) = r
  simp
  ring
end GlobalTheory.SW.HeatTerm
