-- Prove2me | solution 1 for GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:00:44.505927+00:00
-- url     : https://prove2.me/submissions/a5f53f9e-bc19-45a8-9035-8e4c2ea97deb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnitFrameEqOrthonormalMulTriangular
import Theorems.Thm_GlobalTheory_UnitFrames_psgn_sq
import Theorems.Thm_GlobalTheory_UnitFrames_lminor_signature
import Theorems.Thm_GlobalTheory_UnitFrames_uMat_conj_eq_signature
import Theorems.Thm_GlobalTheory_UnitFrames_det_uMat
import Theorems.Thm_GlobalTheory_UnitFrames_inv_uMat_upper
import Theorems.Thm_GlobalTheory_UnitFrames_inv_uMat_diag
import Theorems.Thm_Formalism_L2_Pj_FJ_gram_eq
import Theorems.Thm_Formalism_L2_Pj_gram_eq
import Theorems.Thm_Formalism_L2_Pj_gram_mul
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_Published_gram_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sgn_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_gram_isHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.UnitFrames
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
namespace GlobalTheory.UnitFrames
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx h1 => ?_, fun x₀ h => ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩,
    fun τ u x₀ hu => ?_⟩
  · refine ⟨fun τ => (mat x τ * uMat (gram τ.1 Gm (mat x τ)) : Matrix _ _ ℂ),
      fun τ => ((uMat (gram τ.1 Gm (mat x τ)))⁻¹ : Matrix _ _ ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
      fun τ => ?_, fun τ i => ?_, ?_⟩
    · show ((uMat (gram τ.1 Gm (mat x τ)))⁻¹).det ≠ 0
      rw [Matrix.det_nonsing_inv, det_uMat]
      simp
    · exact inv_uMat_upper _ hca
    · show gram τ.1 Gm (mat x τ * uMat (gram τ.1 Gm (mat x τ))) = _
      rw [FrameDegreeData.gram_mul]
      exact uMat_conj_eq_signature p0 _ (gram_isHermitian τ.1 hG _) (hx τ).2 (h1 τ)
    · show ‖(uMat (gram τ.1 Gm (mat x τ)))⁻¹ i i‖ = 1
      rw [inv_uMat_diag, norm_one]
    · funext τ
      show mat x τ = (mat x τ * uMat (gram τ.1 Gm (mat x τ))) * (uMat (gram τ.1 Gm (mat x τ)))⁻¹
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_uMat]; exact isUnit_one)]
  · intro h0
    have h2 := congrArg Matrix.det (h τ)
    rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h2
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
    rcases sgn_sq p0 k with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature, Complex.ofReal_re]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [FrameDegreeData.gram_mul, FrameDegreeData.gram_eq τ Gm u, hu, FrameDegreeData.gram_eq]
end GlobalTheory.UnitFrames
