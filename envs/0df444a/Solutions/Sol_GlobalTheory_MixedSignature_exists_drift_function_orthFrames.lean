-- Prove2me | solution 1 for GlobalTheory.MixedSignature.exists_drift_function_orthFrames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:39.517683+00:00
-- url     : https://prove2.me/submissions/d607d42f-1871-491e-bc65-f3abe503468b

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
import Theorems.Thm_GlobalTheory_MixedSignature_height_sup_lact_invariant
import Theorems.Thm_GlobalTheory_MixedSignature_minGe_of_lines
import Theorems.Thm_GlobalTheory_MixedSignature_weighted_sup_drift_on_orthonormal_frames
import Theorems.Thm_GlobalTheory_DriftUnitary_continuous_orbit
import Theorems.Thm_GlobalTheory_FiniteCovolume_nonneg_of_isLUB_image
import Theorems.Thm_GlobalTheory_FiniteCovolume_weighted_sup_drift_on_orthonormal_frames
import Theorems.Thm_GlobalTheory_HeightEnds_gramDet_square
import Theorems.Thm_GlobalTheory_HeightInv_relIndex_span_map
import Theorems.Thm_GlobalTheory_HeightLower_exists_pos_le_height
import Theorems.Thm_GlobalTheory_LineHeight_c_pos
import Theorems.Thm_GlobalTheory_LineHeight_exists_min_le_of_le_prod
import Theorems.Thm_GlobalTheory_LineHeight_gramDet_column
import Theorems.Thm_GlobalTheory_LineHeight_nonempty_cmType
import Theorems.Thm_GlobalTheory_SubspaceHeight_exists_height
import Theorems.Thm_GlobalTheory_exists_isLUB_height_rpow_lowerSemicontinuousOn
import Theorems.Thm_GlobalTheory_height_sup_lact_invariant
import Theorems.Thm_GlobalTheory_lowerSemicontinuousOn_sum_pos_mul
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
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
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (_ : G.det ≠ 0) (τ0 : X.Ψ), 0 < p τ0 → p τ0 < r → ∀ (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p τ0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | Orth X G p x} ∧ (∀ x, Orth X G p x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab G X.Λ γ → ∀ x, Orth X G p x → f (lact γ x) = f x) ∧ (∀ x, Orth X G p x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, Orth X G p x → f x ≤ M → MinGe X ε x) := by
  intro r X G p hG τ0 hp0 hpr S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.SubspaceHeight.exists_height r X
  obtain ⟨δ, hδ, hdrift⟩ := weighted_sup_drift_on_orthonormal_frames r X G p hG d hd τ0 S hS hirr hU
  obtain ⟨α, hα, hlsc⟩ := GlobalTheory.exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hineq⟩ := hdrift α hα
  have hinv : ∀ x, Orth X G p x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 :=
    fun x hx => det_ne_zero_of_isOrth X hx
  have hdpos : ∀ x, Orth X G p x → ∀ W, 0 < d x W := by
    intro x hx W
    obtain ⟨m, hm, hW⟩ := GlobalTheory.HeightLower.exists_pos_le_height r X d hd x (hinv x hx)
    exact hm.trans_le (hW W)
  have hαnn : ∀ x, Orth X G p x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := E) (M := Fin r → E) (n := i)
      (by simpa using hi)
    have hW : Module.finrank E (Submodule.span E (Set.range v)) = i := by
      simpa using finrank_span_eq_card hv
    exact (Real.rpow_nonneg (hdpos x hx _).le _).trans
      ((hα i hi x (hinv x hx)).1 ⟨_, hW, rfl⟩)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hineq, ?_⟩
  · refine lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi => ?_
    exact (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hinv x hx
  · intro x hx
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [height_sup_lact_invariant r X d hd δ α hα γ hγ x (hinv x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have hM' : 0 < max 1 (M / e 1) := lt_max_of_lt_left one_pos
    obtain ⟨ε, hε, hla⟩ := minGe_of_lines r X d hd ((max 1 (M / e 1)) ^ (-δ)⁻¹)
      (Real.rpow_pos_of_pos hM' _)
    refine ⟨ε, hε, fun x hx hM => hla x (hinv x hx) fun W hW => ?_⟩
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨one_pos, by omega⟩
    have h2 : e 1 * α 1 x ≤ M :=
      (Finset.single_le_sum (f := fun i => e i * α i x) (fun i hi =>
        mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)) h1).trans hM
    have h3 : α 1 x ≤ M / e 1 := by
      rw [le_div_iff₀ (he 1), mul_comm]; exact h2
    have h4 : d x W ^ (-δ) ≤ max 1 (M / e 1) :=
      (((hα 1 (by omega) x (hinv x hx)).1 ⟨W, hW, rfl⟩).trans h3).trans (le_max_right _ _)
    exact (Real.rpow_inv_le_iff_of_neg hM' (hdpos x hx W) (by linarith)).2 h4
end GlobalTheory.MixedSignature
