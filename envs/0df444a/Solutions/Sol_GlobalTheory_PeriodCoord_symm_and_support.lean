-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.symm_and_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:42.543493+00:00
-- url     : https://prove2.me/submissions/5b46300f-a132-4187-9c3c-50e2455317fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_imForm_apply
import Theorems.Thm_GlobalTheory_PeriodCoord_riemann_symm
import Theorems.Thm_GlobalTheory_PeriodCoord_ext_period
import Theorems.Thm_GlobalTheory_PeriodCoord_comm_of_realMap
import Theorems.Thm_GlobalTheory_PeriodCoord_comm_herm
import Theorems.Thm_GlobalTheory_PeriodConn_hermForm_conj_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ty P₀) (hP : IsPeriod D ty P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) (i j : Fin g) :
    ((A⁻¹ * B)ᵀ * M₀) i j = ((A⁻¹ * B)ᵀ * M₀) j i ∧
      (ty j ≠ ComplexEmbedding.conjugate (ty i) → ((A⁻¹ * B)ᵀ * M₀) i j = 0) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  constructor
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_period hP₀ fun x => ext_period hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) i j
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · intro hij
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, ty j (a : E) ≠ ComplexEmbedding.conjugate (ty i) (a : E) := by
      by_contra hc
      push Not at hc
      exact hij (IsFractionRing.ringHom_ext (A := 𝓞 E) hc)
    obtain ⟨h1, h2⟩ := comm_of_realMap hP₀ hP h a
    have h3 : actMat ty a * (A⁻¹ * B) = A⁻¹ * B * actMat ty (H.bar a) := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (actMat ty a * A) * A⁻¹ = A⁻¹ * (A * actMat ty a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    have h4 : (A⁻¹ * B)ᵀ * M₀ * actMat ty a = actMat ty (H.bar a) * ((A⁻¹ * B)ᵀ * M₀) := by
      have := congrArg transpose h3
      rw [transpose_mul, transpose_mul (A⁻¹ * B), actMat, actMat, diagonal_transpose, diagonal_transpose] at this
      rw [Matrix.mul_assoc, ← comm_herm hP₀ hM₀, ← Matrix.mul_assoc, ← Matrix.mul_assoc, actMat, actMat, this]
    have h5 := congrFun (congrFun h4 i) j
    rw [actMat, actMat, mul_diagonal, diagonal_mul, H.bar_eq, IsCMField.complexEmbedding_complexConj] at h5
    rw [ComplexEmbedding.conjugate_coe_eq] at ha
    have h6 : ((A⁻¹ * B)ᵀ * M₀) i j * (ty j (a : E) - conj (ty i (a : E))) = 0 := by linear_combination h5
    exact (mul_eq_zero.1 h6).resolve_right (sub_ne_zero.2 ha)
end GlobalTheory.PeriodCoord
