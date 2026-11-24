-- Prove2me | solution 1 for GlobalTheory.UnitaryLog.exists_log_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:08.908022+00:00
-- url     : https://prove2.me/submissions/cfd4a20f-8fbd-4be6-901b-3aaaa5742244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
namespace GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma linftyOp_norm_le_mul_of_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ δ) : ‖A‖ ≤ n * δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : A = 0 := Subsingleton.elim _ _
    simp [this]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (h ⟨0, hn⟩ ⟨0, hn⟩)
  lift δ to NNReal using hδ
  rw [linfty_opNorm_def]
  have key : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ n • δ := by
    refine Finset.sup_le fun i _ => ?_
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => ‖A i j‖₊) δ
      (fun j _ => by exact_mod_cast h i j)
    simpa using this
  have := (NNReal.coe_le_coe.2 key)
  simpa [nsmul_eq_mul] using this
open Matrix Filter Topology in
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma norm_entry_le_linftyOp_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  rw [linfty_opNorm_def]
  calc ‖A i j‖ = ((‖A i j‖₊ : NNReal) : ℝ) := rfl
    _ ≤ ((∑ k, ‖A i k‖₊ : NNReal) : ℝ) := by
      exact_mod_cast Finset.single_le_sum (f := fun k => ‖A i k‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := by
      exact_mod_cast Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)
end GlobalTheory.UnitaryLog
end

set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.UnitaryLog
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
open Matrix Filter Topology
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace GlobalTheory.UnitaryLog
namespace _root_.GlobalTheory.UnitaryLog
theorem _root_.solution (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ →
      (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧
        NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  set L := hf.localInverse _ _ _ with hL
  set φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => G⁻¹ * Xᴴ * G with hφ
  have hφc : Continuous φ :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa [φ] using hφc.tendsto 0
  have hleft : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X :=
    hf.eventually_left_inverse
  have hP : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X ∧
      L (NormedSpace.exp (φ X)) = φ X ∧ L (NormedSpace.exp (-X)) = -X :=
    hleft.and ((hφ0.eventually hleft).and
      ((continuous_neg.tendsto' (0 : Matrix (Fin n) (Fin n) ℂ) 0 neg_zero).eventually hleft))
  obtain ⟨K, s, hs, hK⟩ := hf.to_localInverse.exists_lipschitzOnWith
  have hQ := hf.eventually_right_inverse.and ((hf.localInverse_tendsto.eventually hP).and hs)
  have hL1 : L (NormedSpace.exp 0) = 0 := hf.localInverse_apply_image
  have hs1 : NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) ∈ s := mem_of_mem_nhds hs
  rw [NormedSpace.exp_zero] at hQ hL1 hs1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hQ
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  refine ⟨ε / (2 * ((n : ℝ) + 1)), K * n, by positivity, ?_⟩
  intro u δ hu hδ hentry
  have hnorm : ‖u - 1‖ ≤ n * δ := linftyOp_norm_le_mul_of_entry_le _ δ hentry
  have hsmall : (n : ℝ) * (ε / (2 * ((n : ℝ) + 1))) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith
  have hdist : dist u 1 < ε := by
    rw [dist_eq_norm]
    calc ‖u - 1‖ ≤ n * δ := hnorm
      _ ≤ n * (ε / (2 * ((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n)
      _ < ε := hsmall
  obtain ⟨hexp, ⟨hX, hXφ, hXneg⟩, hus⟩ := hball hdist
  refine ⟨L u, ?_, hexp, ?_⟩
  · have hGu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hG
    have hinv : u⁻¹ = G⁻¹ * uᴴ * G := by
      apply Matrix.inv_eq_left_inv
      have hu' := hu
      simp only [Matrix.mul_assoc] at hu' ⊢
      rw [hu', Matrix.nonsing_inv_mul G hG]
    have hexpφ : NormedSpace.exp (φ (L u)) = NormedSpace.exp (-L u) := by
      rw [Matrix.exp_neg, hexp, hinv]
      simp only [φ]
      rw [Matrix.exp_conj' G _ hGu, Matrix.exp_conjTranspose, hexp]
    have heq : φ (L u) = -L u := by
      rw [← hXφ, ← hXneg, hexpφ]
    calc (L u)ᴴ * G + G * L u = G * φ (L u) + G * L u := by
          simp only [φ]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
            Matrix.one_mul]
      _ = 0 := by rw [heq, Matrix.mul_neg, neg_add_cancel]
  · intro i j
    calc ‖L u i j‖ ≤ ‖L u‖ := norm_entry_le_linftyOp_norm _ i j
      _ = dist (L u) (L 1) := by rw [hL1, dist_zero_right]
      _ ≤ K * dist u 1 := hK.dist_le_mul u hus 1 hs1
      _ ≤ K * (n * δ) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
      _ = K * n * δ := by ring
end _root_.GlobalTheory.UnitaryLog
end GlobalTheory.UnitaryLog
