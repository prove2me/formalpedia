-- Prove2me | solution 1 for GlobalTheory.WeilM.eventually_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:26:50.464108+00:00
-- url     : https://prove2.me/submissions/3e13d857-4853-4062-8326-fd0fcfa3db72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
namespace GlobalTheory.WeilM
theorem _root_.solution {P V : Type} [TopologicalSpace P] [TopologicalSpace V] {p₀ : P} (f g : P → V → V)
    (hf : Continuous fun q : P × V => f q.1 q.2) (hg : Continuous fun q : P × V => g q.1 q.2)
    (f0 : ∀ v, f p₀ v = v) (g0 : ∀ v, g p₀ v = v) (hgf : ∀ p v, g p (f p v) = v) {φ : V → ℂ} (hφ : φ ∈ SB V) :
    ∀ᶠ p in 𝓝 p₀, ∀ v, φ (f p v) = φ v := by
  have key : ∀ f : P → V → V, (Continuous fun q : P × V => f q.1 q.2) → (∀ v, f p₀ v = v) →
      ∀ᶠ p in 𝓝 p₀, ∀ v ∈ tsupport φ, φ (f p v) = φ v := fun f hf f0 => by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hφ.1.comp_continuous hf).eventually_eq (p₀, v),
      (hφ.1.comp_continuous continuous_snd).eventually_eq (p₀, v)] with q h1 h2
    simp only [Function.comp, f0] at h1 h2
    rw [h1, h2]
  filter_upwards [key f hf f0, key g hg g0] with p h1 h2 v
  by_cases hv : v ∈ tsupport φ
  · exact h1 v hv
  · by_cases hw : f p v ∈ tsupport φ
    · rw [← h2 _ hw, hgf]
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]
end GlobalTheory.WeilM
