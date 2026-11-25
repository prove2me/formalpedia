-- Prove2me | solution 1 for GlobalTheory.OrthNear.dmin_cpt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:57.361392+00:00
-- url     : https://prove2.me/submissions/86c8b4d5-9e42-4714-8eb8-c913322e5702

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DminCptEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_IW_V_zero_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mulVec_eq_sum_col
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
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
namespace GlobalTheory.OrthNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem mat_cpt_eq_mat_mul_mat_nmat {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_mul_apply_eq_sum {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M N : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * N) = Matrix.of fun a b =>
      ∑ c, ∑ d, N c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G M c d * starRingEnd ℂ (N d b) := by
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * N) a = ∑ c, N c a • _root_.ReciprocityTheory.ChartRestriction.G.FD.col M c := by
    intro a
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mulVec_eq_sum_col]
    ext k
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, hcol, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_chartCoord_orthonormal_indep_lemma {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ) := by
  have hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) :=
    (hx τ).trans (hy τ).symm
  rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, gram_mul_apply_eq_sum, gram_mul_apply_eq_sum, hx']
end GlobalTheory.OrthNear
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.OrthNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OrthNear
namespace _root_.GlobalTheory.OrthNear
theorem _root_.solution {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ i := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_chartCoord_orthonormal_indep_lemma X hx hy z τ]
end _root_.GlobalTheory.OrthNear
end GlobalTheory.OrthNear
