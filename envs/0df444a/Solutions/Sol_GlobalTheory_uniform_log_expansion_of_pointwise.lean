-- Prove2me | solution 1 for GlobalTheory.uniform_log_expansion_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:57.260571+00:00
-- url     : https://prove2.me/submissions/b4f29242-afc2-4c08-8bf3-ab2ac4f49d58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UniformLogExpansionOfPointwise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma re_det_gram_mul_eq_normSq_det_mul {r i : ℕ} (B : Matrix (Fin r) (Fin i) ℂ)
    (X : Matrix (Fin i) (Fin i) ℂ) :
    ((B * X)ᴴ * (B * X)).det.re = Complex.normSq X.det * (Bᴴ * B).det.re := by
  have h : (B * X)ᴴ * (B * X) = Xᴴ * (Bᴴ * B) * X := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [h, det_mul, det_mul, det_conjTranspose, Complex.star_def,
    show (starRingEnd ℂ) X.det * (Bᴴ * B).det * X.det
      = ((Complex.normSq X.det : ℝ) : ℂ) * (Bᴴ * B).det by
        rw [Complex.normSq_eq_conj_mul_self]; ring,
    Complex.re_ofReal_mul]
open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma norm_apply_le_one_of_conjTranspose_mul_self_eq_one {r i : ℕ} (Q : Matrix (Fin r) (Fin i) ℂ)
    (hQ : Qᴴ * Q = 1) (j : Fin r) (k : Fin i) : ‖Q j k‖ ≤ 1 := by
  have h := congrFun (congrFun hQ k) k
  simp only [Matrix.mul_apply, conjTranspose_apply, one_apply_eq] at h
  have h' : ∑ l, Complex.normSq (Q l k) = 1 := by
    have : ∑ l, ((Complex.normSq (Q l k) : ℝ) : ℂ) = 1 := by
      rw [← h]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    exact_mod_cast this
  have hle : Complex.normSq (Q j k) ≤ 1 :=
    h' ▸ Finset.single_le_sum (fun l _ => Complex.normSq_nonneg (Q l k)) (Finset.mem_univ j)
  rw [Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (Q j k)]
open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma exists_mul_right_orthonormal_of_re_det_gram_pos {r i : ℕ} (M : Matrix (Fin r) (Fin i) ℂ)
    (hM : 0 < (Mᴴ * M).det.re) :
    ∃ X : Matrix (Fin i) (Fin i) ℂ, (M * X)ᴴ * (M * X) = 1 := by
  have hPSD := Matrix.posSemidef_conjTranspose_mul_self M
  have hunit : IsUnit (Mᴴ * M) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h; rw [h] at hM; simp at hM
  have hPD := hPSD.posDef_iff_isUnit.mpr hunit
  have hpos := hPD.eigenvalues_pos
  have hspec := hPD.1.spectral_theorem
  have hUU : star (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) *
      (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hPD.1.eigenvectorUnitary.2
  simp only [Unitary.conjStarAlgAut_apply] at hspec
  generalize hPD.1.eigenvalues = lam at hpos hspec
  generalize (hPD.1.eigenvectorUnitary : Matrix (Fin i) (Fin i) ℂ) = U at hspec hUU
  refine ⟨U * diagonal (fun k => ((Real.sqrt (lam k))⁻¹ : ℂ)), ?_⟩
  have e1 : ∀ X : Matrix (Fin i) (Fin i) ℂ, (M * X)ᴴ * (M * X) = Xᴴ * (Mᴴ * M) * X := by
    intro X; simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e1, hspec, conjTranspose_mul, ← star_eq_conjTranspose U]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
    Matrix.one_mul, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext k
  have hk := hpos k
  have hs0 : ((Real.sqrt (lam k) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hs' : ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hk.le
  change star ((Real.sqrt (lam k) : ℂ))⁻¹ * (((lam k : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℂ))⁻¹) = 1
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← hs']
  field_simp
open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
private lemma exists_pos_uniform_le_sum_log_ratio_det_gram {r i : ℕ}
    (S : Finset (Matrix (Fin r) (Fin r) ℂ))
    (hpt : ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (Mᴴ * M).det.re →
      (∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re) ∧
      0 < ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re)) :
    ∃ η : ℝ, 0 < η ∧ ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (Mᴴ * M).det.re →
      η ≤ ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) := by
  set F : Matrix (Fin r) (Fin i) ℂ → ℝ :=
    fun M => ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) with hF
  set K : Set (Matrix (Fin r) (Fin i) ℂ) := {Q | Qᴴ * Q = 1} with hK
  have hK1 : ∀ Q ∈ K, 0 < (Qᴴ * Q).det.re := by
    intro Q hQ
    rw [show Qᴴ * Q = 1 from hQ]
    simp
  have hinv : ∀ (M : Matrix (Fin r) (Fin i) ℂ) (X : Matrix (Fin i) (Fin i) ℂ),
      (M * X)ᴴ * (M * X) = 1 → F (M * X) = F M := by
    intro M X hX
    have hone : Complex.normSq X.det * (Mᴴ * M).det.re = 1 := by
      rw [← re_det_gram_mul_eq_normSq_det_mul, hX]; simp
    have hs : Complex.normSq X.det ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hone; exact zero_ne_one hone
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show a * (M * X) = a * M * X from (Matrix.mul_assoc _ _ _).symm,
      re_det_gram_mul_eq_normSq_det_mul, re_det_gram_mul_eq_normSq_det_mul, mul_div_mul_left _ _ hs]
  have hgram : ∀ B : Matrix (Fin r) (Fin i) ℂ → Matrix (Fin r) (Fin i) ℂ, Continuous B →
      Continuous fun Q => ((B Q)ᴴ * B Q).det.re := by
    intro B hB
    exact Complex.continuous_re.comp
      ((hB.matrix_conjTranspose.matrix_mul hB).matrix_det)
  have hclosed : IsClosed K :=
    isClosed_eq ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id) continuous_const
  have hcomp : IsCompact K := by
    refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed ?_
    intro Q hQ
    simp only [Set.mem_pi, Set.mem_univ, Metric.mem_closedBall, dist_zero_right, forall_const]
    exact fun j k => norm_apply_le_one_of_conjTranspose_mul_self_eq_one Q hQ j k
  have hcont : ContinuousOn F K := by
    refine continuousOn_finset_sum _ fun a _ => ?_
    refine ContinuousOn.log ?_ ?_
    · refine ((hgram _ (continuous_const.matrix_mul continuous_id)).continuousOn).div
        (hgram _ continuous_id).continuousOn ?_
      exact fun Q hQ => (hK1 Q hQ).ne'
    · intro Q hQ
      exact (div_pos ((hpt Q (hK1 Q hQ)).1 a ‹_›) (hK1 Q hQ)).ne'
  by_cases hne : K.Nonempty
  · obtain ⟨Q₀, hQ₀, hmin⟩ := hcomp.exists_isMinOn hne hcont
    refine ⟨F Q₀, (hpt Q₀ (hK1 Q₀ hQ₀)).2, fun M hM => ?_⟩
    obtain ⟨X, hX⟩ := exists_mul_right_orthonormal_of_re_det_gram_pos M hM
    show F Q₀ ≤ F M
    rw [← hinv M X hX]
    exact hmin (show M * X ∈ K from hX)
  · refine ⟨1, one_pos, fun M hM => ?_⟩
    obtain ⟨X, hX⟩ := exists_mul_right_orthonormal_of_re_det_gram_pos M hM
    exact absurd ⟨M * X, hX⟩ hne
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  intro hpt r S hS hirr
  have key : ∀ i : ℕ, ∃ η : ℝ, 0 < η ∧ (0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ,
      0 < (Mᴴ * M).det.re →
      η ≤ ∑ a ∈ S, Real.log (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re)) := by
    intro i
    by_cases hi : 0 < i ∧ i < r
    · obtain ⟨η, hη, h⟩ := exists_pos_uniform_le_sum_log_ratio_det_gram S
        (fun M hM => hpt r S hS hirr i hi.1 hi.2 M hM)
      exact ⟨η, hη, fun _ _ => h⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hi⟩
  choose η hη hb using key
  have hmem1 : (1 : ℝ) ∈ (Finset.range r).image η ∪ {1} :=
    Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  refine ⟨((Finset.range r).image η ∪ {1}).min' ⟨1, hmem1⟩, ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finset.min'_mem _ ⟨1, hmem1⟩) with hy | hy
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hy
      rw [← hj]
      exact hη j
    · rw [Finset.mem_singleton.mp hy]; exact one_pos
  · intro i hi hir M hM
    exact (Finset.min'_le _ _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem η (Finset.mem_range.mpr hir)))).trans (hb i hi hir M hM)
end _root_.GlobalTheory
end GlobalTheory
