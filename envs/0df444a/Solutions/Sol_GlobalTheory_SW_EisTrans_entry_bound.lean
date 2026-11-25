-- Prove2me | solution 1 for GlobalTheory.SW.EisTrans.entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:38:50.956645+00:00
-- url     : https://prove2.me/submissions/7f8955d3-0aa3-4b18-93d0-738ba437c6bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaEisensteinConvergeBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Theorems.Thm_GlobalTheory_SW_TransComp_key
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SW.rowEmb_apply
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisTrans
variable {N : ℕ}
namespace GlobalTheory.SW.EisTrans
theorem _root_.solution {C D Z : Matrix (Fin N) (Fin N) ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : D * Cᴴ = C * Dᴴ) (hQ : (C * Z + D).det ≠ 0)
    (hZ : (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) (i j : Fin N) :
    ‖((C * Z + D)⁻¹ * C) i j‖ ≤ δ⁻¹ := by
  have e0 : (C * Z + D) * Cᴴ - C * (C * Z + D)ᴴ = C * (Z - Zᴴ) * Cᴴ := by
    rw [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, h]; noncomm_ring
  generalize C * Z + D = Q at e0 hQ
  have hi : Q⁻¹ * Q = 1 := nonsing_inv_mul Q (Ne.isUnit hQ)
  have hi' : Qᴴ * (Q⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, hi, conjTranspose_one]
  have e1 : (Q⁻¹ * C) * (Z - Zᴴ) * (Q⁻¹ * C)ᴴ = (Q⁻¹ * C)ᴴ - Q⁻¹ * C := by
    calc _ = Q⁻¹ * (C * (Z - Zᴴ) * Cᴴ) * (Q⁻¹)ᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Q⁻¹ * Q) * (Cᴴ * (Q⁻¹)ᴴ) - Q⁻¹ * C * (Qᴴ * (Q⁻¹)ᴴ) := by rw [← e0]; noncomm_ring
      _ = _ := by rw [hi, hi', conjTranspose_mul, Matrix.one_mul, Matrix.mul_one]
  generalize Q⁻¹ * C = S at e1
  have key : δ * ∑ k, ‖S i k‖ ^ 2 ≤ ‖S i i‖ := by
    have h1 := (hZ.mul_mul_conjTranspose_same S).diag_nonneg (i := i)
    rw [Matrix.mul_sub, Matrix.sub_mul, imH, Matrix.mul_smul, Matrix.smul_mul, e1,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at h1
    have h2 : (S * Sᴴ) i i = ((∑ k, ‖S i k‖ ^ 2 : ℝ) : ℂ) := by
      simp [Matrix.mul_apply, Complex.mul_conj']
    have h3 : (2 * I)⁻¹ * (conj (S i i) - S i i) = ((-(S i i).im : ℝ) : ℂ) := by
      rw [← neg_sub, Complex.sub_conj]; push_cast; field_simp
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, h2, conjTranspose_apply,
      Complex.star_def, h3] at h1
    have h4 : (0 : ℝ) ≤ -(S i i).im - δ * ∑ k, ‖S i k‖ ^ 2 := by exact_mod_cast h1
    have h5 := (abs_le.1 (Complex.abs_im_le_norm (S i i))).1
    linarith
  have hs : ∀ k, δ * ‖S i k‖ ^ 2 ≤ ‖S i i‖ := fun k => le_trans (mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun k => ‖S i k‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ k)) hδ.le) key
  have a1 : δ * ‖S i i‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 0 < ‖S i i‖ := by by_contra h0; nlinarith [norm_nonneg (S i i)]
    nlinarith [hs i]
  rw [← one_div, le_div_iff₀ hδ]
  by_contra hc
  push Not at hc
  nlinarith [hs j, mul_le_mul_of_nonneg_left (hs j) hδ.le]
end GlobalTheory.SW.EisTrans
