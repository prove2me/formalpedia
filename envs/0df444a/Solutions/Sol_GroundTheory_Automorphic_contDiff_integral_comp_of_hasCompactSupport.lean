-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiff_integral_comp_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:31.771276+00:00
-- url     : https://prove2.me/submissions/ba6ba96c-4eb2-4e6a-8b2e-3d2a57f61a73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open MeasureTheory
namespace GroundTheory.Automorphic
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] (ν : Measure X)
    [IsFiniteMeasure ν] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {u : X → V}
    (hu : Continuous u) (n : ℕ) :
    ∀ {W F : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [CompleteSpace F] (Ξ : V × W → F), ContDiff ℝ ∞ Ξ → HasCompactSupport Ξ →
      ContDiff ℝ n (fun z => ∫ x, Ξ (u x, z) ∂ν) := by
  induction n with
  | zero =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    obtain ⟨C, hC⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    rw [Nat.cast_zero, contDiff_zero]
    refine continuous_of_dominated (bound := fun _ => C) (fun z => ?_) (fun z => ?_)
      (integrable_const C) (Eventually.of_forall fun a => ?_)
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a => hC _
    · exact hΞ.continuous.comp (continuous_const.prodMk continuous_id)
  | succ n ih =>
    intro W F _ _ _ _ _ Ξ hΞ hc
    set Ξ' : V × W → (W →L[ℝ] F) := fun q => (fderiv ℝ Ξ q).comp (ContinuousLinearMap.inr ℝ V W)
      with hΞ'def
    have hΞ'c : ContDiff ℝ ∞ Ξ' :=
      ContDiff.clm_comp (𝕜 := ℝ) (g := fun q => fderiv ℝ Ξ q)
        (f := fun _ => ContinuousLinearMap.inr ℝ V W)
        (hΞ.fderiv_right (m := ∞) (by simp)) contDiff_const
    have hΞ's : HasCompactSupport Ξ' :=
      (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : V × W →L[ℝ] F => L.comp (ContinuousLinearMap.inr ℝ V W))
        (ContinuousLinearMap.zero_comp _)
    obtain ⟨C, hC⟩ := hΞ'c.continuous.bounded_above_of_compact_support hΞ's
    obtain ⟨C₀, hC₀⟩ := hΞ.continuous.bounded_above_of_compact_support hc
    have hdiff : ∀ (v : V) (z : W), HasFDerivAt (fun z => Ξ (v, z)) (Ξ' (v, z)) z := by
      intro v z
      have h1 : HasFDerivAt Ξ (fderiv ℝ Ξ (v, z)) (v, z) :=
        ((hΞ.differentiable (by simp)) (v, z)).hasFDerivAt
      exact h1.comp z ((hasFDerivAt_const v z).prodMk (hasFDerivAt_id z))
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun z => ∫ x, Ξ' (u x, z) ∂ν, ih Ξ' hΞ'c hΞ's, fun z₀ => ?_⟩
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := fun _ => C)
      (F := fun z a => Ξ (u a, z)) (F' := fun z a => Ξ' (u a, z))
      univ_mem (Eventually.of_forall fun z => ?_) ?_ ?_ ?_ (integrable_const C) ?_
    · exact (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Integrable.of_bound
        (hΞ.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable C₀
        (Eventually.of_forall fun a => hC₀ _)
    · exact (hΞ'c.continuous.comp (hu.prodMk continuous_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun a z _ => hC _
    · exact Eventually.of_forall fun a z _ => hdiff (u a) z
end GroundTheory.Automorphic
