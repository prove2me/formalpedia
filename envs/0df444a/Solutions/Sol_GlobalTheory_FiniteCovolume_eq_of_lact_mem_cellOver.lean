-- Prove2me | solution 1 for GlobalTheory.FiniteCovolume.eq_of_lact_mem_cellOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:08:01.127122+00:00
-- url     : https://prove2.me/submissions/aaf76a2c-b5f6-4779-9d55-6eb41f35d232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
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
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
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


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem mat_rmul' {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ := by rfl
private theorem mat_lact' {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (γ : GL (Fin r) K) (x : Frame Ψ r) (τ : Ψ) :
    mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) K).map τ.1 * mat x τ := by rfl
private theorem frame_ext_of_mat_eq {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {x y : Frame Ψ r}
    (h : ∀ τ, mat x τ = mat y τ) : x = y :=
  funext fun τ => h τ
private theorem rmul_rmul_eq_rmul_rmul {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (x b c : Frame Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) :=
  frame_ext_of_mat_eq fun τ => by simp only [mat_rmul', Matrix.mul_assoc]
private theorem blockTriangular_mat_of_mem_bor {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).BlockTriangular id := by
  intro i j h
  exact (hb τ).2 i j h
private theorem rmul_mem_Bor {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : c ∈ Bor Ψ r) : rmul b c ∈ Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a d h => ?_⟩
  · rw [mat_rmul', Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · exact ((blockTriangular_mat_of_mem_bor hb τ).mul (blockTriangular_mat_of_mem_bor hc τ)) h
private theorem exists_bor_right_inverse {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) :
    ∃ c : Frame Ψ r, c ∈ Bor Ψ r ∧ ∀ x : Frame Ψ r, rmul (rmul x b) c = x := by
  refine ⟨fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_,
    fun x => frame_ext_of_mat_eq fun τ => ?_⟩
  · have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
    let _ := Matrix.invertibleOfIsUnitDet _ hu
    refine ⟨(Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, fun a c h => ?_⟩
    exact (Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_mat_of_mem_bor hb τ)) h
  · show mat x τ * mat b τ * (mat b τ)⁻¹ = mat x τ
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]
private theorem lact_mul_torus_haar_measure {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (γ γ' : GL (Fin r) K) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) :=
  frame_ext_of_mat_eq fun τ => by
    simp only [mat_lact', Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
private theorem lact_one_torus_haar_measure {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (x : Frame Ψ r) : lact 1 x = x :=
  frame_ext_of_mat_eq fun τ => by
    rw [mat_lact', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
private theorem lact_rmul_torus_haar_measure {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (γ : GL (Fin r) K) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b :=
  frame_ext_of_mat_eq fun τ => by
    simp only [mat_lact', mat_rmul', Matrix.mul_assoc]
end GlobalTheory.FiniteCovolume
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FiniteCovolume
theorem _root_.solution {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {δ δ' : GL (Fin r) E} (hδ : δ ∈ X.Γ) (hδ' : δ' ∈ X.Γ)
    (h : lact δ x ∈ cellOver X x0 FF) (h' : lact δ' x ∈ cellOver X x0 FF) : δ = δ' := by
  obtain ⟨⟨z, c⟩, ⟨hz, hc⟩, hx⟩ := h
  obtain ⟨⟨z', c'⟩, ⟨hz', hc'⟩, hx'⟩ := h'
  dsimp only at hx hx'
  obtain ⟨cinv, hcinv, hcc⟩ := exists_bor_right_inverse hc'
  have hγ : δ' * δ⁻¹ ∈ X.Γ := X.Γ.mul_mem hδ' (X.Γ.inv_mem hδ)
  have hbb : rmul c cinv ∈ Bor X.Ψ r := rmul_mem_Bor hc hcinv
  have hkey : cpt X x0 z' = lact (δ' * δ⁻¹) (rmul (cpt X x0 z) (rmul c cinv)) := by
    rw [← rmul_rmul_eq_rmul_rmul, hx, lact_rmul_torus_haar_measure, ← lact_mul_torus_haar_measure, inv_mul_cancel_right, ← hx', hcc]
  have hzz : z = z' := hFF.2.2.1 z hz z' hz' _ hγ _ hbb hkey
  rw [← hzz] at hkey
  have hdom : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  have h1 : lact (δ' * δ⁻¹)⁻¹ (cpt X x0 z) = rmul (cpt X x0 z) (rmul c cinv) := by
    conv_lhs => rw [hkey]
    rw [← lact_mul_torus_haar_measure, inv_mul_cancel, lact_one_torus_haar_measure]
  have h2 := X.Γ_free _ (X.Γ.inv_mem hγ) _ hdom _ hbb h1
  rw [inv_eq_one, mul_inv_eq_one] at h2
  exact h2.symm
end GlobalTheory.FiniteCovolume
