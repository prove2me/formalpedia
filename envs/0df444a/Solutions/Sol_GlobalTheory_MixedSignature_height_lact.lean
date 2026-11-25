-- Prove2me | solution 1 for GlobalTheory.MixedSignature.height_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:20.567255+00:00
-- url     : https://prove2.me/submissions/8150b9f9-95d9-4bf5-8ed3-64f7ab92be86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeights
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSubspaceHeightGramDeterminant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteMeasureCoverOfDriftFunction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetReNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIsLUBHeightRpowLowerSemicontinuousOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightRpowNegDistortionContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedHeightSupDriftOrthonormalFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionOrthonormalHermitianFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDriftFunctionRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeightedSupDriftOnOrthonormalFrames
import Theorems.Thm_GlobalTheory_DriftUnitary_continuous_orbit
import Theorems.Thm_GlobalTheory_FiniteCovolume_nonneg_of_isLUB_image
import Theorems.Thm_GlobalTheory_HeightEnds_gramDet_square
import Theorems.Thm_GlobalTheory_HeightInv_relIndex_span_map
import Theorems.Thm_GlobalTheory_LatBasis_exists_basis_mem
import Theorems.Thm_GlobalTheory_LineHeight_c_pos
import Theorems.Thm_GlobalTheory_LineHeight_exists_min_le_of_le_prod
import Theorems.Thm_GlobalTheory_LineHeight_gramDet_column
import Theorems.Thm_GlobalTheory_LineHeight_nonempty_cmType
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MixedSignature
open GlobalTheory.HeightInv (relIndex_span_map)
open GlobalTheory.HeightEnds (gramDet_square)
open GlobalTheory.LineHeight (gramDet_column exists_min_le_of_le_prod nonempty_cmType c_pos)
open GlobalTheory.FiniteCovolume (nonneg_of_isLUB_image)
open GlobalTheory.DriftUnitary (continuous_orbit)
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MixedSignature
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0) ∧ ∀ W : Submodule E (Fin r → E), d (lact γ x) (W.map (γ : Matrix (Fin r) (Fin r) E).mulVecLin) = d x W) := by
  intro r X G d hd γ hγ x hx
  have hmat : ∀ τ : X.Ψ, mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ :=
    fun τ => rfl
  have hγdet : (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hτdet : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    have := τ.1.map_det (γ : Matrix (Fin r) (Fin r) E)
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (map_ne_zero τ.1).2 hγdet
  have hx' : ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 := by
    intro τ
    rw [hmat, Matrix.det_mul]
    exact mul_ne_zero (hτdet τ) (hx τ)
  refine ⟨hx', fun W => ?_⟩
  obtain ⟨w, hw, hwΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  set f := (γ : Matrix (Fin r) (Fin r) E).mulVecLin with hf
  have hinj : Function.Injective f := Matrix.mulVec_injective_of_isUnit γ.isUnit
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.1 hinj
  have hΛ : ∀ y, y ∈ X.Λ ↔ f y ∈ X.Λ := hγ.2
  have hw' : LinearIndependent E (fun a => f (w a)) :=
    hw.map' f (LinearMap.ker_eq_bot.2 hinj)
  have hsp' : W.map f = Submodule.span E (Set.range fun a => f (w a)) := by
    conv_lhs => rw [← hsp]
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have e1 := hd (lact γ x) hx' _ (fun a => f (w a)) hw' (fun a => (hΛ _).1 (hwΛ a))
  have e2 := hd x hx _ w hw hwΛ
  have hM : ∀ τ : X.Ψ, (mat (lact γ x) τ)⁻¹ * (Matrix.of fun k a => τ.1 (f (w a) k)) =
      (mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)) := by
    intro τ
    have : (Matrix.of fun k a => τ.1 (f (w a) k)) =
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (Matrix.of fun k a => τ.1 (w a k)) := by
      ext k a
      simp [hf, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [this, hmat, Matrix.mul_inv_rev, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hτdet τ).isUnit]
  rw [hsp', e1, relIndex_span_map X.Λ f hinj hsurj hΛ w]
  rw [hsp] at e2
  rw [e2, hsp]
  simp only [hM]
end GlobalTheory.MixedSignature
