-- Prove2me | solution 1 for GlobalTheory.FiniteCovolume.cpt_mem_cellOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:07:59.842808+00:00
-- url     : https://prove2.me/submissions/e088c2aa-198d-42cb-ab65-0cb068b155fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
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
private theorem frame_ext_of_mat_eq {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {x y : Frame Ψ r}
    (h : ∀ τ, mat x τ = mat y τ) : x = y :=
  funext fun τ => h τ
private theorem blockTriangular_mat_of_mem_bor {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).BlockTriangular id := by
  intro i j h
  exact (hb τ).2 i j h
private theorem exists_bor_right_identity {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} :
    ∃ o : Frame Ψ r, o ∈ Bor Ψ r ∧ ∀ x : Frame Ψ r, rmul x o = x := by
  refine ⟨fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c h => ?_⟩,
    fun x => frame_ext_of_mat_eq fun τ => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · exact Matrix.one_apply_ne h.ne'
  · exact Matrix.mul_one (mat x τ)
private theorem gram_eq_lemma {K : Type} [Field K] {r : ℕ} (τ : K →+* ℂ) (G : Matrix (Fin r) (Fin r) K)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
private theorem det_mat_ne_zero_of_isOrth_frame {r : ℕ} {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro hdet
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_lemma, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, zero_mul, zero_mul,
    Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) h.symm
  unfold sgn
  split_ifs <;> norm_num
private theorem mat_nmat_diag_eq_one {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    mat (nmat X z) τ a a = 1 := by
  simp [mat, nmat]
private theorem blockTriangular_mat_nmat_lower {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
  intro a c h
  have h' : a < c := OrderDual.toDual_lt_toDual.1 h
  simp [mat, nmat, not_lt.2 h'.le, h'.ne]
private theorem det_mat_nmat_eq_one {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (blockTriangular_mat_nmat_lower X z τ)]
  simp [mat_nmat_diag_eq_one]
private theorem eq_of_mat_nmat_eq {r : ℕ} (X : Data E r) {z z' : V (nd X)}
    (h : ∀ τ, mat (nmat X z) τ = mat (nmat X z') τ) : z = z' := by
  ext k
  rcases he : (Fintype.equivFin (Ent X)).symm k with ⟨τ, ⟨⟨a, c⟩, hac⟩⟩
  have h1 := congrFun (congrFun (h τ) a) c
  have hk : k = Fintype.equivFin (Ent X) ⟨τ, ⟨(a, c), hac⟩⟩ := by
    rw [← he]
    exact ((Fintype.equivFin (Ent X)).apply_symm_apply k).symm
  simp only [mat, nmat, Matrix.of_apply, dif_pos hac] at h1
  rw [hk]
  exact h1
private theorem eq_of_rmul_cpt_eq_rmul_cpt {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {z z' : V (nd X)} {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') : z = z' ∧ b = b' := by
  have hN : ∀ τ, mat (nmat X z) τ = mat (nmat X z') τ := by
    intro τ
    have h1 := congrArg (fun y => mat y τ) h
    simp only [cpt, mat_rmul', Matrix.mul_assoc] at h1
    have hu0 : IsUnit (mat x0 τ) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_mat_ne_zero_of_isOrth_frame ho τ))
    have h2 := hu0.mul_left_cancel h1
    have huN' : IsUnit (mat (nmat X z') τ).det := by
      rw [det_mat_nmat_eq_one]
      exact isUnit_one
    have huB : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
    have hD : (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ = mat b' τ * (mat b τ)⁻¹ := by
      calc (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ
          = (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ * (mat b τ * (mat b τ)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ huB, Matrix.mul_one]
        _ = (mat (nmat X z') τ)⁻¹ * (mat (nmat X z) τ * mat b τ) * (mat b τ)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (mat (nmat X z') τ)⁻¹ * (mat (nmat X z') τ * mat b' τ) * (mat b τ)⁻¹ := by rw [h2]
        _ = mat b' τ * (mat b τ)⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huN', Matrix.one_mul]
    have hlow : ((mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
      let _ := Matrix.invertibleOfIsUnitDet _ huN'
      exact (Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_mat_nmat_lower X z' τ)).mul
        (blockTriangular_mat_nmat_lower X z τ)
    have hup : (mat b' τ * (mat b τ)⁻¹).BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet _ huB
      exact (blockTriangular_mat_of_mem_bor hb' τ).mul (Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_mat_of_mem_bor hb τ))
    have hoff : ∀ i j, i ≠ j → ((mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ) i j = 0 := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact hlow (OrderDual.toDual_lt_toDual.2 hlt)
      · rw [hD]
        exact hup hlt
    have hNeq : mat (nmat X z) τ =
        mat (nmat X z') τ * ((mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huN', Matrix.one_mul]
    have hone : (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        have h3 := congrFun (congrFun hNeq i) i
        rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff k i hki, mul_zero])
          (by simp), mat_nmat_diag_eq_one, mat_nmat_diag_eq_one, one_mul] at h3
        rw [Matrix.one_apply_eq]
        exact h3.symm
      · rw [hoff i j hij, Matrix.one_apply_ne hij]
    rw [hNeq, hone, Matrix.mul_one]
  have hz := eq_of_mat_nmat_eq X hN
  subst hz
  refine ⟨rfl, frame_ext_of_mat_eq fun τ => ?_⟩
  have h1 := congrArg (fun y => mat y τ) h
  simp only [mat_rmul'] at h1
  have hu : IsUnit (mat (cpt X x0 z) τ) := by
    refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ?_)
    rw [cpt, mat_rmul', Matrix.det_mul, det_mat_nmat_eq_one, mul_one]
    exact det_mat_ne_zero_of_isOrth_frame ho τ
  exact hu.mul_left_cancel h1
end GlobalTheory.FiniteCovolume
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FiniteCovolume
theorem _root_.solution {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} {z : V (nd X)} : cpt X x0 z ∈ cellOver X x0 FF ↔ z ∈ FF := by
  obtain ⟨o, ho1, ho2⟩ := exists_bor_right_identity (Ψ := X.Ψ) (r := r)
  constructor
  · rintro ⟨⟨z', c⟩, ⟨hz', hc⟩, hx⟩
    dsimp only at hx
    have hzz := eq_of_rmul_cpt_eq_rmul_cpt X ho hc ho1 (hx.trans (ho2 _).symm)
    exact hzz.1 ▸ hz'
  · intro hz
    exact ⟨(z, o), ⟨hz, ho1⟩, ho2 _⟩
end GlobalTheory.FiniteCovolume
