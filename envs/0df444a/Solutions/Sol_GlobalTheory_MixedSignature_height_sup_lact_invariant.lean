-- Prove2me | solution 1 for GlobalTheory.MixedSignature.height_sup_lact_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:04.671824+00:00
-- url     : https://prove2.me/submissions/7bb3cb7a-c9fe-4655-a81d-2ab4ec44e548

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
import Theorems.Thm_GlobalTheory_MixedSignature_height_lact
import Theorems.Thm_GlobalTheory_DriftUnitary_continuous_orbit
import Theorems.Thm_GlobalTheory_FiniteCovolume_nonneg_of_isLUB_image
import Theorems.Thm_GlobalTheory_HeightEnds_gramDet_square
import Theorems.Thm_GlobalTheory_HeightInv_height_lact
import Theorems.Thm_GlobalTheory_HeightInv_relIndex_span_map
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
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) {G : Matrix (Fin r) (Fin r) E} (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (δ : ℝ) (α : ℕ → Frame X.Ψ r → ℝ), (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ i ≤ r, α i (lact γ x) = α i x) := by
  intro r X G d hd δ α hα γ hγ x hx i hi
  obtain ⟨hx', hinv⟩ := height_lact r X d hd γ hγ x hx
  let e : (Fin r → E) ≃ₗ[E] (Fin r → E) := Matrix.GeneralLinearGroup.toLin γ |>.toLinearEquiv
  have he : (e : (Fin r → E) →ₗ[E] (Fin r → E)) = (γ : Matrix (Fin r) (Fin r) E).mulVecLin := by
    ext1 j
    rfl
  rw [← he] at hinv
  refine (hα i hi _ hx').unique ?_
  suffices hs : (fun W => d (lact γ x) W ^ (-δ)) '' {W | Module.finrank E W = i} =
      (fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i} by
    rw [hs]
    exact hα i hi x hx
  ext t
  constructor
  · rintro ⟨W, hW, rfl⟩
    refine ⟨W.map (e.symm : (Fin r → E) →ₗ[E] (Fin r → E)), ?_, ?_⟩
    · simpa [LinearEquiv.finrank_map_eq] using hW
    · show d x _ ^ (-δ) = d (lact γ x) W ^ (-δ)
      rw [← hinv, ← Submodule.map_comp]
      simp
  · rintro ⟨W, hW, rfl⟩
    refine ⟨W.map (e : (Fin r → E) →ₗ[E] (Fin r → E)), ?_, ?_⟩
    · simpa [LinearEquiv.finrank_map_eq] using hW
    · show d (lact γ x) _ ^ (-δ) = d x W ^ (-δ)
      rw [hinv]
end GlobalTheory.MixedSignature
