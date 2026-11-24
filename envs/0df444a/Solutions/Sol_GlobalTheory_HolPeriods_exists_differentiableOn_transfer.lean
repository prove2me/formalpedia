-- Prove2me | solution 1 for GlobalTheory.HolPeriods.exists_differentiableOn_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:36:14.569688+00:00
-- url     : https://prove2.me/submissions/2852ccef-ea07-4e24-a7af-dd49e5375e6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods
namespace GlobalTheory.HolPeriods
theorem _root_.solution {V Λ : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup Λ]
    {g : ℕ} {B : Set V} (hB : IsOpen B) {Q Q' : V → (Λ →+ (Fin g → ℂ))}
    (hQ : ∀ x, DifferentiableOn ℂ (fun b => Q b x) B) (hQ' : ∀ x, DifferentiableOn ℂ (fun b => Q' b x) B)
    {b₀ : V} (hb₀ : b₀ ∈ B) (hspan : Submodule.span ℝ (Set.range (Q b₀)) = ⊤)
    (k : V → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hk : ∀ b ∈ B, ∀ x, Q' b x = k b (Q b x)) :
    ∃ B' : Set V, IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => k bz.1 bz.2) (B' ×ˢ Set.univ) := by
  classical
  have hc : ∀ i : Fin g, ∃ c : Λ →₀ ℝ, (c.sum fun a r => r • Q b₀ a) = Pi.single i 1 := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (by rw [hspan]; trivial)
  choose c hc using hc
  let M : (V → (Λ →+ (Fin g → ℂ))) → V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun R b =>
    ∑ i, (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).smulRight
      (∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • R b a)
  have hM : ∀ R : V → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => R b x) B) →
      DifferentiableOn ℂ (M R) B := by
    intro R hR
    refine DifferentiableOn.fun_sum fun i _ => ?_
    refine ((ContinuousLinearMap.smulRightL ℂ (Fin g → ℂ) (Fin g → ℂ)
      (ContinuousLinearMap.proj i)).differentiable.comp_differentiableOn ?_)
    exact DifferentiableOn.fun_sum fun a _ => (hR a).fun_const_smul _
  have h0 : M Q b₀ = 1 := by
    ext1 z
    have : ∀ i, ∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • Q b₀ a = Pi.single i 1 := fun i => by
      rw [← hc i]; simp [Finsupp.sum]
    simp only [M, this, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.one_apply]
    ext j; simp [Pi.single_apply]
  have hkM : ∀ b ∈ B, ∀ z, k b (M Q b z) = M Q' b z := by
    intro b hb z
    simp [M, map_sum, hk b hb]
  refine ⟨B ∩ M Q ⁻¹' {x | IsUnit x}, (hM Q hQ).continuousOn.isOpen_inter_preimage hB Units.isOpen,
    ⟨hb₀, by simp [h0]⟩, Set.inter_subset_left, ?_⟩
  have hd : DifferentiableOn ℂ (fun b => M Q' b * Ring.inverse (M Q b)) (B ∩ M Q ⁻¹' {x | IsUnit x}) := by
    refine ((hM Q' hQ').mono Set.inter_subset_left).mul fun b hb => ?_
    exact (differentiableAt_inverse hb.2).comp_differentiableWithinAt b
      ((hM Q hQ).mono Set.inter_subset_left b hb)
  have hd2 : DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => (M Q' bz.1 * Ring.inverse (M Q bz.1)) bz.2)
      ((B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ) :=
    (hd.comp differentiableOn_fst fun bz hbz => hbz.1).clm_apply differentiableOn_snd
  refine hd2.congr fun bz hbz => ?_
  rw [ContinuousLinearMap.mul_apply, ← hkM _ hbz.1.1, ← ContinuousLinearMap.mul_apply,
    Ring.mul_inverse_cancel _ hbz.1.2, ContinuousLinearMap.one_apply]
end GlobalTheory.HolPeriods
