-- Prove2me | solution 1 for GlobalTheory.SW.HAct.group_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:39.07507+00:00
-- url     : https://prove2.me/submissions/65dca530-5492-46c6-b45e-8803ba68d420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_one
import Theorems.Thm_GlobalTheory_SW_HAct_left_inv
import Theorems.Thm_GlobalTheory_SW_Base_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_SW_Base_ccT_one


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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {γ : M2 E N} (h : γ ∈ UU E N) :
    IsUnit γ.det ∧ γ⁻¹ ∈ UU E N ∧ ccT γ ∈ UU E N ∧
      γ⁻¹ = -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) := by
  have h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  have hl := left_inv h
  have hu : IsUnit γ.det := Matrix.isUnit_det_of_left_inverse hl
  have hi : γ * γ⁻¹ = 1 := mul_nonsing_inv γ hu
  refine ⟨hu, ?_, ?_, Matrix.inv_eq_left_inv hl⟩
  · change ccT γ⁻¹ * Matrix.J (Fin N) E * γ⁻¹ = Matrix.J (Fin N) E
    calc _ = ccT γ⁻¹ * (ccT γ * Matrix.J (Fin N) E * γ) * γ⁻¹ := by rw [h1]
      _ = ccT (γ * γ⁻¹) * Matrix.J (Fin N) E * (γ * γ⁻¹) := by
        simp only [ccT_mul, Matrix.mul_assoc]
      _ = _ := by rw [hi, ccT_one, Matrix.one_mul, Matrix.mul_one]
  · change ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E
    rw [ccT_ccT]
    have hr : γ * -(Matrix.J (Fin N) E * ccT γ * Matrix.J (Fin N) E) = 1 := mul_eq_one_comm.1 hl
    have h2 := congrArg (· * Matrix.J (Fin N) E) hr
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, Matrix.J_squared, Matrix.mul_one,
      neg_neg, Matrix.one_mul] at h2
    rw [Matrix.mul_assoc, h2]
end GlobalTheory.SW.HAct
