-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ClosedSubgroup.exists_nhds_kernel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:21.266104+00:00
-- url     : https://prove2.me/submissions/8bac7e9a-1a8a-4ae0-8051-399d7b012cce

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLogMemLieAlg
import Theorems.Thm_GlobalTheory_CompanionTheory_ClosedSubgroup_exp_neg_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_ClosedSubgroup_exp_smul_limit_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ClosedSubgroup
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
namespace GlobalTheory.CompanionTheory.ClosedSubgroup
theorem _root_.solution {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (p : A →L[ℝ] A) (hp : ∀ Z ∈ S, p Z = Z) :
    ∃ W₀ ∈ 𝓝 (0 : A), ∀ Y ∈ W₀, NormedSpace.exp Y ∈ G → p Y = 0 → Y = 0 := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ Y : A, ‖Y‖ < 1 / ((k : ℝ) + 1) ∧ NormedSpace.exp Y ∈ G ∧ p Y = 0 ∧ Y ≠ 0 := by
    intro k
    obtain ⟨Y, hY, hYG, hYp, hY0⟩ :=
      hcon (Metric.ball 0 (1 / ((k : ℝ) + 1))) (Metric.ball_mem_nhds _ (by positivity))
    exact ⟨Y, by simpa using hY, hYG, hYp, hY0⟩
  choose Y hYn hYG hYp hY0 using hseq
  have hpos : ∀ k, 0 < ‖Y k‖ := fun k => norm_pos_iff.2 (hY0 k)
  have hsph : ∀ k, (‖Y k‖)⁻¹ • Y k ∈ Metric.sphere (0 : A) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos k).ne']
  haveI : ProperSpace A := FiniteDimensional.proper ℝ A
  obtain ⟨b, hb, φ, hφ, hlim⟩ := (isCompact_sphere (0 : A) 1).tendsto_subseq hsph
  have hε : Tendsto (fun k => ‖Y k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun k => (hYn k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hεφ : Tendsto (fun k => ‖Y (φ k)‖) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  have hmem : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • b) ∈ G := by
    intro t ht
    refine exp_smul_limit_mem hc h1 hmul (ε := fun k => ‖Y (φ k)‖)
      (a := fun k => (‖Y (φ k)‖)⁻¹ • Y (φ k)) (fun k => hpos _) hεφ hlim (fun k => ?_) ht
    have : ‖Y (φ k)‖ • (‖Y (φ k)‖)⁻¹ • Y (φ k) = Y (φ k) := by
      rw [smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]
    simpa only [this] using hYG (φ k)
  have hbS : b ∈ S := by
    refine (hS b).2 fun t => ?_
    rcases le_total 0 t with ht | ht
    · exact hmem t ht
    · have := exp_neg_mem hinv (hmem (-t) (by linarith))
      simpa using this
  have hpb : p b = 0 := by
    have h2 : Tendsto (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) atTop (𝓝 (p b)) :=
      (p.continuous.tendsto b).comp hlim
    have h3 : (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) = fun _ => 0 := by
      funext k
      rw [map_smul, hYp, smul_zero]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  have hb0 : b = 0 := by rw [← hp b hbS, hpb]
  have hb1 : ‖b‖ = 1 := mem_sphere_zero_iff_norm.1 hb
  rw [hb0, norm_zero] at hb1
  exact zero_ne_one hb1
end GlobalTheory.CompanionTheory.ClosedSubgroup
