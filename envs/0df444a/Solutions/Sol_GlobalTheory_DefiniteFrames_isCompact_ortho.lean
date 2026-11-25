-- Prove2me | solution 1 for GlobalTheory.DefiniteFrames.isCompact_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:15.035002+00:00
-- url     : https://prove2.me/submissions/8767839b-ec5f-41c0-b547-81ff77004223

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsCompactOfDefinite
import Theorems.Thm_PIW_FdPA_det_ne_of_gram
import Theorems.Thm_PIW_FdPA_gram_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
namespace GlobalTheory.DefiniteFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma exists_diagonal_sgn_eq_smul_one (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    ∃ c : ℂ, c ≠ 0 ∧
      (Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = c • 1 := by
  rcases hp with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    ext a b
    by_cases hab : a = b <;> simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h, hab]
  · refine ⟨1, one_ne_zero, ?_⟩
    ext a b
    have ha : (a : ℕ) < X.p0 := lt_of_lt_of_le a.isLt h
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hab]
open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma norm_apply_le_sum_of_gram_eq_smul_one {n : ℕ} (G M M₀ : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : c ≠ 0) (h₀ : M₀.det ≠ 0)
    (hM₀ : M₀.transpose * G * M₀.map (starRingEnd ℂ) = c • 1)
    (hM : M.transpose * G * M.map (starRingEnd ℂ) = c • 1) (i j : Fin n) :
    ‖M i j‖ ≤ ∑ k, ‖M₀ i k‖ := by
  obtain ⟨V, rfl⟩ : ∃ V, M = M₀ * V :=
    ⟨M₀⁻¹ * M, (Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr h₀)).symm⟩
  have hVV : V.transpose * V.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.transpose_mul, Matrix.map_mul] at hM
    have h : V.transpose * (M₀.transpose * G * M₀.map (starRingEnd ℂ)) * V.map (starRingEnd ℂ)
        = c • 1 := by
      rw [← hM]; simp only [Matrix.mul_assoc]
    rw [hM₀, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h
    exact smul_right_injective _ hc h
  have hVV' : V.map (starRingEnd ℂ) * V.transpose = 1 := mul_eq_one_comm.mp hVV
  have hbound : ∀ a b, ‖V a b‖ ≤ 1 := by
    intro a b
    have h := congrFun (congrFun hVV' a) a
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at h
    have hs : ∑ k, Complex.normSq (V a k) = 1 := by
      have h' : ((∑ k, Complex.normSq (V a k) : ℝ) : ℂ) = 1 := by
        rw [← h]; push_cast; simp [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast h'
    have hle : Complex.normSq (V a b) ≤ 1 :=
      hs ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (V a k)) (Finset.mem_univ b)
    rw [Complex.normSq_eq_norm_sq] at hle
    nlinarith [norm_nonneg (V a b)]
  rw [Matrix.mul_apply]
  calc ‖∑ k, M₀ i k * V k j‖ ≤ ∑ k, ‖M₀ i k * V k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖M₀ i k‖ := Finset.sum_le_sum fun k _ => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hbound k j)
end GlobalTheory.DefiniteFrames
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory GlobalTheory.DefiniteFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.DefiniteFrames
namespace _root_.GlobalTheory.DefiniteFrames
theorem _root_.solution (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    IsCompact {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} := by
  obtain ⟨c, hc, hD⟩ := exists_diagonal_sgn_eq_smul_one X hp
  rcases Set.eq_empty_or_nonempty {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} with he | ⟨x₀, hx₀⟩
  · rw [he]; exact isCompact_empty
  have hgram : ∀ {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}, X.IsOrtho x → ∀ τ : X.Ψ,
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).transpose * X.Gm.map (τ : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).map (starRingEnd ℂ)
        = c • 1 := by
    intro x hx τ
    rw [← _root_.PIW.FdPA.gram_eq, ← hD]
    exact hx τ
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ).det ≠ 0 := fun τ =>
    _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm _ (by rw [_root_.PIW.FdPA.gram_eq, hgram hx₀ τ]; simp [hc])
  have hU : ∀ τ : X.Ψ, Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := fun τ =>
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun τ => Set.univ.pi fun i =>
      Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) (∑ k, ‖x₀ τ i k‖))
    (isCompact_univ_pi fun τ => isCompact_univ_pi fun i => isCompact_univ_pi fun _ =>
      isCompact_closedBall _ _) ?_ ?_
  · simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    simp only [_root_.PIW.FdPA.gram_eq]
    exact ((hU τ).matrix_transpose.matrix_mul continuous_const).matrix_mul
      ((hU τ).matrix_map Complex.continuous_conj)
  · intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro τ i j
    exact norm_apply_le_sum_of_gram_eq_smul_one (X.Gm.map (τ : E →+* ℂ)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ) c hc (hdet τ) (hgram hx₀ τ) (hgram hx τ) i j
end _root_.GlobalTheory.DefiniteFrames
end GlobalTheory.DefiniteFrames
