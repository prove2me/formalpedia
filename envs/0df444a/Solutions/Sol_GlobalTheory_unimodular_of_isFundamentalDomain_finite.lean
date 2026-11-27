-- Prove2me | solution 1 for GlobalTheory.unimodular_of_isFundamentalDomain_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:21.487512+00:00
-- url     : https://prove2.me/submissions/833b339f-c8c4-48ba-8925-35fed64cf051

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnimodularOfIsFundamentalDomainFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal ENNReal
open MeasureTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S : Type) [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S] (Γ : Subgroup S) [Countable Γ] (μS : Measure S) (𝓢 : Set S), μS.IsHaarMeasure → IsFundamentalDomain Γ 𝓢 μS → μS 𝓢 ≠ ⊤ → μS.IsMulRightInvariant := by
  intro S _ _ _ _ _ _ _ _ Γ _ μS 𝓢 hH hF hfin
  haveI : SMulInvariantMeasure Γ S μS :=
    ⟨fun c s _ => by
      show μS ((fun x => (c : S) * x) ⁻¹' s) = μS s
      exact measure_preimage_mul μS (c : S) s⟩
  have hpos : μS 𝓢 ≠ 0 := hF.measure_ne_zero (NeZero.ne μS)
  refine ⟨fun g => ?_⟩
  have hmap := Measure.map_right_mul_eq_modularCharacterFun_smul μS g

  have hF' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' 𝓢) μS := by
    refine hF.preimage_of_equiv (e := id) ?_ Function.bijective_id ?_
    · exact quasiMeasurePreserving_mul_right μS g
    · intro γ x
      show (γ : S) * x * g = (γ : S) * (x * g)
      exact mul_assoc _ _ _
  have heq : μS ((fun x => x * g) ⁻¹' 𝓢) = μS 𝓢 := hF'.measure_eq hF
  have h2 : (Measure.map (fun x => x * g) μS) 𝓢 = μS 𝓢 := by
    rw [show (fun x : S => x * g) = ⇑(MeasurableEquiv.mulRight g) from rfl, MeasurableEquiv.map_apply]
    exact heq
  rw [hmap] at h2
  rw [Measure.smul_apply] at h2
  have hc : (Measure.modularCharacterFun g : ℝ≥0∞) = 1 := by
    have h3 : (Measure.modularCharacterFun g : ℝ≥0∞) * μS 𝓢 = 1 * μS 𝓢 := by
      rw [one_mul]; simpa [ENNReal.smul_def] using h2
    exact (ENNReal.mul_left_inj hpos hfin).mp h3
  rw [show (fun x : S => x * g) = fun x => x * g from rfl] at hmap
  rw [hmap]
  have : Measure.modularCharacterFun g = 1 := by exact_mod_cast hc
  rw [this, one_smul]
end GlobalTheory
