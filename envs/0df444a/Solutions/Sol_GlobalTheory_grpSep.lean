-- Prove2me | solution 1 for GlobalTheory.grpSep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:34.960665+00:00
-- url     : https://prove2.me/submissions/f4e60709-3dc2-4e85-9fa4-0831c847e171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsLeNormDev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.AR.Up.IW.V_zero_app


section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.GrpSep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.GrpSep
namespace GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma sgn_ne_zero_torus_haar_measure (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma det_mat_ne_zero_of_isOrth' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (τ : X.Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (h τ)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at this
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast sgn_ne_zero_torus_haar_measure X.p0 a) this.symm
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_dom_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) : x0 ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  refine fun τ => ⟨det_mat_ne_zero_of_isOrth' X h τ, fun i => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [h τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  rw [← Complex.ofReal_prod, Complex.ofReal_re,
    Fin.prod_univ_eq_prod_range (fun j => _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j) i]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  exact mul_self_pos.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => sgn_ne_zero_torus_haar_measure X.p0 a)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma continuous_shift' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    Continuous (fun M : Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : Ψ → Fin r → Fin r → ℂ)) := by
  unfold _root_.GlobalTheory.GrpSep.shift _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul ((continuous_apply τ).add continuous_const)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_zero_torus_haar_measure {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.GlobalTheory.GrpSep.shift x0 0 = x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * (0 + 1) = x0 τ
  rw [zero_add, Matrix.mul_one]; rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_pos_le_of_finite_pos {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) : ∃ δ > 0, ∀ a ∈ S, δ ≤ f a := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨a0, ha0, hmin⟩ := Set.exists_min_image S f hS h
    exact ⟨f a0, hf a0 ha0, hmin⟩
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma oneF_mem_bor {Ψ : Finset (E →+* ℂ)} {r : ℕ} :
    _root_.GlobalTheory.GrpSep.oneF Ψ r ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
  refine fun τ => ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · change (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne h.ne'
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_dev_eq_lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r)
    (hdet : ∀ τ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0) (γ : GL (Fin r) E) :
    _root_.GlobalTheory.GrpSep.shift x0 (_root_.GlobalTheory.GrpSep.dev x0 γ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1 + 1) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  rw [sub_add_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mul]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rmul_oneF' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x0 (_root_.GlobalTheory.GrpSep.oneF Ψ r) = x0 := by
  funext τ
  change (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * 1 : Matrix (Fin r) (Fin r) ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  exact Matrix.mul_one _
end GlobalTheory
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r),
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X →
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r),
      c ≤ ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1) a b‖ := by
  intro r X x0 hO hP
  have hdom := mem_dom_of_isOrth X hO
  have hdet := det_mat_ne_zero_of_isOrth' X hO
  obtain ⟨U, hU, U', hU', hfin⟩ := hP x0 hdom x0 hdom
  have hV : (fun M : X.Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : X.Ψ → Fin r → Fin r → ℂ)) ⁻¹' U' ∈
      nhds (0 : X.Ψ → Fin r → Fin r → ℂ) :=
    (continuous_shift' x0).continuousAt.preimage_mem_nhds (by erw [shift_zero_torus_haar_measure]; exact hU')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨δ, hδ, hmin⟩ := exists_pos_le_of_finite_pos _ (hfin.subset Set.diff_subset)
    (fun γ => ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖) (by
      rintro γ ⟨hγ, h1⟩
      refine norm_pos_iff.mpr fun h0 => h1 ?_
      refine X.Γ_free γ hγ.1 x0 hdom (_root_.GlobalTheory.GrpSep.oneF X.Ψ r) oneF_mem_bor ?_
      rw [← shift_dev_eq_lact x0 hdet, rmul_oneF']
      exact (congrArg (_root_.GlobalTheory.GrpSep.shift x0) h0).trans (shift_zero_torus_haar_measure x0))
  refine ⟨min ε δ, lt_min hε hδ, fun γ hγ h1 => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖ < min ε δ := by
    refine (pi_norm_lt_iff (lt_min hε hδ)).mpr fun τ => (pi_norm_lt_iff (lt_min hε hδ)).mpr
      fun a => (pi_norm_lt_iff (lt_min hε hδ)).mpr fun b => hcon τ a b
  have hmem : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 ∈ U' := by
    rw [← shift_dev_eq_lact x0 hdet]
    exact hball (mem_ball_zero_iff.mpr (hlt.trans_le (min_le_left _ _)))
  have hS := hmin γ ⟨⟨hγ, x0, mem_of_mem_nhds hU, _, hmem, _root_.GlobalTheory.GrpSep.oneF X.Ψ r,
    oneF_mem_bor, (rmul_oneF' _).symm⟩, h1⟩
  exact absurd hS (not_le.mpr (hlt.trans_le (min_le_right _ _)))
end _root_.GlobalTheory
end GlobalTheory
