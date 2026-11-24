-- Prove2me | solution 1 for GlobalTheory.exists_localFrame_compatible_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:53.631871+00:00
-- url     : https://prove2.me/submissions/111d2727-5b61-460b-a429-6a9596828d7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLocalFrameCompatibleCube
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro H1 H2 g ι W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp
  obtain ⟨i₀, hi₀⟩ := hcov 0
  obtain ⟨F, hF⟩ : ∃ F, F = T (fun _ => i₀) := ⟨_, rfl⟩
  let U : Set (Fin 3 → Fin g → ℂ) := {x | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W i₀}
  have hUo : IsOpen U := by
    have e : U = ⋂ I : Finset (Fin 3), (fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a) ⁻¹' W i₀ := by
      ext x
      simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun I =>
      (hW i₀).preimage (continuous_finsetSum I fun a _ => continuous_apply a)
  have hU0 : (0 : Fin 3 → Fin g → ℂ) ∈ U := fun I => by simpa using hi₀
  have hUn : U ∈ 𝓝 (0 : Fin 3 → Fin g → ℂ) := hUo.mem_nhds hU0
  have hFa : AnalyticAt ℂ F 0 := hF ▸ GlobalTheory.SCV.analyticAt_of_differentiableOn (hTd _) hUn
  have hF0 : F 0 ≠ 0 := hF ▸ hT0 _ 0 hU0
  have hcube := H1 g W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp i₀ hi₀ F hF
  obtain ⟨k, hka, -, hkF⟩ := H2 g F hFa hF0 hcube
  obtain ⟨ε, hε, hkε⟩ : ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Fin g → ℂ) ε, DifferentiableAt ℂ k z :=
    Metric.eventually_nhds_iff_ball.1 (hka.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 (hW i₀) 0 hi₀
  have hrW : ∀ z ∈ Metric.ball (0 : Fin g → ℂ) (min ε δ), z ∈ W i₀ := fun z hz =>
    hδW (Metric.ball_subset_ball (min_le_right _ _) hz)
  refine ⟨min ε δ, fun i z => c i i₀ z * cexp (k z), F 0, lt_min hε hδ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    show DifferentiableOn ℂ (fun z => c i i₀ z * cexp (k z)) _
    refine DifferentiableOn.mul ((hcd i i₀).mono ?_) ?_
    · rintro z ⟨hz1, hz2⟩
      exact ⟨hz1, hrW z hz2⟩
    · intro z hz
      exact (hkε z (Metric.ball_subset_ball (min_le_left _ _) hz.2)).cexp.differentiableWithinAt
  · intro i z hz hzr
    exact mul_ne_zero (hc0 i i₀ z hz (hrW z hzr)) (Complex.exp_ne_zero _)
  · intro i j z hzi hzj hzr
    show c i i₀ z * cexp (k z) = c i j z * (c j i₀ z * cexp (k z))
    rw [← mul_assoc, hcoc i j i₀ z hzi hzj (hrW z hzr)]
  · filter_upwards [hkF, hUn] with x hx hxU
    intro j hj
    rw [hTc j (fun _ => i₀) x hj hxU, ← hF, hx]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    ring
end GlobalTheory
