-- Prove2me | solution 1 for GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:45.229511+00:00
-- url     : https://prove2.me/submissions/b4597a64-6553-4d8b-818d-ea3cd9676041

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_NormBcharMulNfacRmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_lminor_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
namespace GlobalTheory.NormFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma nfac_eq_prod_norm_dmin_ratio_rpow {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la x = ∏ τ, ∏ i : Fin r,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma blockTriangular_id_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r)
    (τ : Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  intro a c hca
  exact (hb τ).2 a c hca
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mat_diag_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (j : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ j j ≠ 0 := by
  have hdet := (show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0 by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb; exact (hb τ).1)
  rw [Matrix.det_of_upperTriangular (blockTriangular_id_of_mem_bor hb τ)] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet j (Finset.mem_univ j)
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    ∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => mat_diag_ne_zero_of_mem_bor hb τ _
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma gram_rmul_eq_transpose_mul_gram {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).transpose * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ) := by
  have hmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
    conv_lhs => unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    rfl
  rw [hmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul]
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma dmin_rmul_eq_diag_prod_mul_conj {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i = (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i * starRingEnd ℂ (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [gram_rmul_eq_transpose_mul_gram]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (blockTriangular_id_of_mem_bor hb τ) i
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_succ {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) :
    ∏ j : Fin (i.succ : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) =
      (∏ j : Fin (i.castSucc : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) * M i i := by
  show ∏ j : Fin ((i : ℕ) + 1), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) = _
  rw [Fin.prod_univ_castSucc]
  rfl
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma norm_ratio_rmul_lemma_2 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.castSucc‖ =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ 2 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
  have hp := diag_prod_ne_zero_of_mem_bor hb τ i.castSucc
  rw [dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.succ, dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.castSucc, diag_prod_succ]
  simp only [norm_div, norm_mul, map_mul, RCLike.norm_conj]
  have hp' : ‖∏ j : Fin (i.castSucc : ℕ), _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)‖ ≠ 0 :=
    norm_ne_zero_iff.2 hp
  by_cases hm : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ = 0
  · simp [hm]
  · field_simp
open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rpow_sq_mul_eq_inv_zpow_mul_rpow {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (l : ℤ) :
    (d ^ 2 * t) ^ (-(l : ℝ) / 2) = (d ^ l)⁻¹ * t ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) ht, ← Real.rpow_natCast, ← Real.rpow_mul hd]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg hd,
    Real.rpow_intCast]
end GlobalTheory.NormFactor
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.NormFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.NormFactor
namespace _root_.GlobalTheory.NormFactor
theorem _root_.solution {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.nfac la x := by
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp_rw [norm_ratio_rmul_lemma_2 X x b hb, rpow_sq_mul_eq_inv_zpow_mul_rpow (norm_nonneg _) (norm_nonneg _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hbc : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ = ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp [norm_prod, norm_zpow]
  have hne : ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (mat_diag_ne_zero_of_mem_bor hb τ i))
  rw [hbc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
end _root_.GlobalTheory.NormFactor
end GlobalTheory.NormFactor
