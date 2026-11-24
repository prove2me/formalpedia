-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:49:08.709746+00:00
-- url     : https://prove2.me/submissions/bb982e6a-0257-4cf3-a540-a586e80c5919

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution (K : ℝ) (U : Set ℂ) (hU : IsOpen U) (Z : Finset ℂ) :
    ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (U \ Z) → (∀ z ∈ U \ (Z : Set ℂ), ‖g z‖ ≤ K) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ (∀ z, z ∉ Z → G z = g z) ∧ ∀ z ∈ U, ‖G z‖ ≤ K := by
  induction Z using Finset.induction_on with
  | empty => intro g h1 h2; exact ⟨g, by simpa using h1, fun _ _ => rfl, by simpa using h2⟩
  | insert a Z ha ih =>
    intro g h1 h2
    have hset : U \ (↑(insert a Z) : Set ℂ) = (U \ Z) \ {a} := by
      ext z; simp; tauto
    rw [hset] at h1 h2
    by_cases haU : a ∈ U
    · have ho : IsOpen (U \ (Z : Set ℂ)) := hU.sdiff Z.finite_toSet.isClosed
      have hn : U \ (Z : Set ℂ) ∈ 𝓝 a := ho.mem_nhds ⟨haU, by simpa using ha⟩
      have hd := Complex.differentiableOn_update_limUnder_of_bddAbove hn h1
        ⟨K, by rintro _ ⟨z, hz, rfl⟩; exact h2 z hz⟩
      obtain ⟨G, g1, g2, g3⟩ := ih _ hd (fun z hz => by
        by_cases hza : z = a
        · subst hza
          have hc : Tendsto (fun w => ‖Function.update g z (limUnder (𝓝[≠] z) g) w‖) (𝓝[≠] z)
              (𝓝 ‖Function.update g z (limUnder (𝓝[≠] z) g) z‖) :=
            ((hd.differentiableAt hn).continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
          refine le_of_tendsto hc ?_
          filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with w hw hw'
          rw [Function.update_of_ne hw]
          exact h2 w ⟨hw', hw⟩
        · rw [Function.update_of_ne hza]; exact h2 z ⟨hz, hza⟩)
      refine ⟨G, g1, fun z hz => ?_, g3⟩
      rw [Finset.mem_insert, not_or] at hz
      rw [g2 z hz.2, Function.update_of_ne hz.1]
    · have : (U \ (Z : Set ℂ)) \ {a} = U \ Z := by
        ext z; constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, fun e => haU (by rw [← Set.mem_singleton_iff.1 e]; exact h.1)⟩
      rw [this] at h1 h2
      obtain ⟨G, g1, g2, g3⟩ := ih g h1 h2
      exact ⟨G, g1, fun z hz => g2 z fun h => hz (Finset.mem_insert_of_mem h), g3⟩
end GlobalTheory.LogDerivHigher
