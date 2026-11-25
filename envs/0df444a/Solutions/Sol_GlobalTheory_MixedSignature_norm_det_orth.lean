-- Prove2me | solution 1 for GlobalTheory.MixedSignature.norm_det_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:07:23.063174+00:00
-- url     : https://prove2.me/submissions/7c1c26e3-5516-4543-8ff4-100cb668aede

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
import Theorems.Thm_GlobalTheory_HeightEnds_gram_eq_mul
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
theorem _root_.solution {r : ℕ} (X : Data E r) {G : Matrix (Fin r) (Fin r) E} {p : X.Ψ → ℕ} (x : Frame X.Ψ r) (hx : Orth X G p x) (τ : X.Ψ) :
    ‖(mat x τ).det‖ ^ 2 * ‖τ.1 G.det‖ = 1 := by
  have h := congrArg (fun M => ‖Matrix.det M‖) (hx τ)
  simp only [GlobalTheory.HeightEnds.gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_conjTranspose,
    Matrix.det_diagonal, norm_mul, norm_star, norm_prod] at h
  have h1 : ∀ a : Fin r, ‖((sgn (p τ) (a : ℕ) : ℝ) : ℂ)‖ = 1 := by
    intro a
    unfold sgn
    split_ifs <;> simp
  simp only [h1, Finset.prod_const_one] at h
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← h]
  ring
end GlobalTheory.MixedSignature
