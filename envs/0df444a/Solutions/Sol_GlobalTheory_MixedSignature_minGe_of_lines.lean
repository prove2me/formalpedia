-- Prove2me | solution 1 for GlobalTheory.MixedSignature.minGe_of_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:23.434952+00:00
-- url     : https://prove2.me/submissions/f5c1c639-3f09-4df0-aa38-7abc7095870a

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
import Theorems.Thm_GlobalTheory_LineHeight_c_pos
import Theorems.Thm_GlobalTheory_LineHeight_exists_min_le_of_le_prod
import Theorems.Thm_GlobalTheory_LineHeight_gramDet_column
import Theorems.Thm_GlobalTheory_LineHeight_nonempty_cmType
import Theorems.Thm_GlobalTheory_SpanIndex_relIndex_span_ne_zero
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
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → (∀ W : Submodule E (Fin r → E), Module.finrank E W = 1 → m ≤ d x W) → MinGe X ε x) := by
  intro r X d hd m hm
  have := nonempty_cmType X
  obtain ⟨τ0, hτ0⟩ := Finite.exists_min X.c
  have hmin : 0 < min 1 m := lt_min one_pos hm
  refine ⟨X.c τ0 * min 1 m, mul_pos (c_pos X τ0) hmin, ?_⟩
  intro x hdet hW v hv hv0
  unfold QuadraticLatticeForms.Qy
  have hli : LinearIndependent E (fun _ : Unit => v) := by
    rw [linearIndependent_unique_iff]; exact hv0
  have hrank : Module.finrank E (Submodule.span E (Set.range (fun _ : Unit => v))) = 1 := by
    rw [finrank_span_eq_card hli]; simp
  have h1 := hW _ hrank
  rw [hd x hdet Unit (fun _ => v) hli (fun _ => hv)] at h1
  have hind := GlobalTheory.SpanIndex.relIndex_span_ne_zero r X Unit (fun _ => v) hli (fun _ => hv)
  have hnn : ∀ τ : X.Ψ, 0 ≤ (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) := fun τ => by
    positivity
  have hprod : (∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k (_ : Unit) => τ.1 (v k)))ᴴ *
      ((mat x τ)⁻¹ * (Matrix.of fun k (_ : Unit) => τ.1 (v k)))).det.re))
      = ∏ τ : X.Ψ, (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) :=
    Finset.prod_congr rfl fun τ _ => by
      exact gramDet_column _ (Data.emb τ.1 v)
  have h2 : m ≤ ∏ τ : X.Ψ, (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) := by
    refine h1.trans ?_
    rw [← hprod]
    refine div_le_self ?_ ?_
    · rw [hprod]; exact Finset.prod_nonneg fun τ _ => hnn τ
    · exact_mod_cast Nat.one_le_iff_ne_zero.2 hind
  obtain ⟨τ, hτ⟩ := exists_min_le_of_le_prod _ hnn m h2
  calc X.c τ0 * min 1 m ≤ X.c τ * (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2) :=
        mul_le_mul (hτ0 τ) hτ hmin.le (c_pos X τ).le
    _ ≤ _ := Finset.single_le_sum (f := fun τ => X.c τ * (∑ a, ‖((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) a‖ ^ 2))
        (fun τ _ => mul_nonneg (c_pos X τ).le (hnn τ)) (Finset.mem_univ τ)
end GlobalTheory.MixedSignature
