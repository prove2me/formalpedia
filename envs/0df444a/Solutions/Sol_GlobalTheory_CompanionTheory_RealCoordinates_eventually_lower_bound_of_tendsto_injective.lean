-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:57:44.866152+00:00
-- url     : https://prove2.me/submissions/0f50b2c0-1b7f-47d8-be4c-d1ff64a6ed82

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniformLowerBoundNearInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RealCoordinates
namespace GlobalTheory.CompanionTheory.RealCoordinates
theorem _root_.solution
    (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ)
    (e : X ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm) (c : P)
    (A : P → X →+ X) (hA : ∀ s, Continuous (A s))
    (hlim : ∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x)))
    (hinj : Function.Injective (A c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  classical

  let f : P → (Fin N → ℝ) →+ (Fin N → ℝ) := fun s =>
    e.toAddMonoidHom.comp ((A s).comp e.symm.toAddMonoidHom)
  have hf : ∀ s, Continuous (f s) := fun s => he.comp ((hA s).comp hes)
  let L : P → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := fun s => (f s).toRealLinearMap (hf s)
  have hL : ∀ s x, e (A s x) = L s (e x) := by
    intro s x
    simp [L, f]
  have hLc : Function.Injective (L c) := by
    intro y z h
    have h' : A c (e.symm y) = A c (e.symm z) := by
      apply e.injective
      simpa [L, f] using h
    simpa using congrArg e (hinj h')

  obtain ⟨K, hK, hKL⟩ := (L c : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hLc)
  have hKpos : (0 : ℝ) < K := hK
  set δ : ℝ := 1 / (2 * K) with hδ
  have hδpos : 0 < δ := by positivity
  have hlow : ∀ y, 2 * δ * ‖y‖ ≤ ‖L c y‖ := by
    intro y
    have h1 := hKL.le_mul_dist y 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
    have h2 : 2 * δ = (K : ℝ)⁻¹ := by
      rw [hδ]
      field_simp
    rw [h2, inv_mul_le_iff₀ hKpos]
    exact h1

  let b : Fin N → Fin N → ℝ := fun i j => if i = j then 1 else 0
  set ε : ℝ := δ / (N + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hev : ∀ᶠ s in nhds c, ∀ i : Fin N, ‖L s (b i) - L c (b i)‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have ht : Filter.Tendsto (fun s => L s (b i)) (nhds c) (nhds (L c (b i))) := by
      have := (he.tendsto _).comp (hlim (e.symm (b i)))
      simpa [L, f, Function.comp_def] using this
    exact (Metric.tendsto_nhds.mp ht ε hεpos).mono fun s hs => by rwa [dist_eq_norm] at hs
  have hNε : (N : ℝ) * ε ≤ δ := by
    rw [hε, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨δ, hδpos, hev.mono fun s hs x => ?_⟩
  rw [hL]
  have hdiff : ‖L s (e x) - L c (e x)‖ ≤ δ * ‖e x‖ := by
    have hy : L s (e x) - L c (e x) = ∑ i, (e x) i • (L s (b i) - L c (b i)) := by
      conv_lhs => rw [pi_eq_sum_univ (e x)]
      simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
      rfl
    rw [hy]
    calc ‖∑ i, (e x) i • (L s (b i) - L c (b i))‖
        ≤ ∑ i, ‖(e x) i • (L s (b i) - L c (b i))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, ‖e x‖ * ε := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm (e x) i) (hs i).le (norm_nonneg _) (norm_nonneg _)
      _ = (N : ℝ) * ε * ‖e x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ δ * ‖e x‖ := mul_le_mul_of_nonneg_right hNε (norm_nonneg _)
  have hc := hlow (e x)
  have htri : ‖L c (e x)‖ ≤ ‖L s (e x)‖ + ‖L s (e x) - L c (e x)‖ := by
    calc ‖L c (e x)‖ = ‖L s (e x) - (L s (e x) - L c (e x))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖L s (e x)‖ + ‖L s (e x) - L c (e x)‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (e x)]
end GlobalTheory.CompanionTheory.RealCoordinates
