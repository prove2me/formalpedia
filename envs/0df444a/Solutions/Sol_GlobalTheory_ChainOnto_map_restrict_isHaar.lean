-- Prove2me | solution 1 for GlobalTheory.ChainOnto.map_restrict_isHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:33.037475+00:00
-- url     : https://prove2.me/submissions/7461a55f-01fb-413f-b701-a394b53d3e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MapRestrictIsHaarOfOpenProductCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.ChainOnto
namespace GlobalTheory.ChainOnto
theorem _root_.solution : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  intro G B _ _ _ _ _ _ _ _ _ _ _ ν _ A i p hA hi hp hpi hiA hK
  have hpm : Measurable p := hp.measurable
  have hAm : MeasurableSet (A : Set G) := hA.measurableSet
  have happ : ∀ S : Set B, MeasurableSet S → Measure.map p (ν.restrict A) S = ν (p ⁻¹' S ∩ A) := by
    intro S hS
    rw [Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]

  have hpre : ∀ S : Set B, p ⁻¹' S ∩ A = (fun x : G × G => x.1 * x.2) '' ((i '' S) ×ˢ {g : G | g ∈ A ∧ p g = 1}) := by
    intro S
    ext g
    constructor
    · rintro ⟨hgS, hgA⟩
      refine ⟨(i (p g), (i (p g))⁻¹ * g), ⟨⟨p g, hgS, rfl⟩, ?_, ?_⟩, by simp⟩
      · exact A.mul_mem (A.inv_mem (hiA _)) hgA
      · simp [hpi]
    · rintro ⟨⟨x, y⟩, ⟨⟨s, hs, rfl⟩, hyA, hy1⟩, rfl⟩
      refine ⟨?_, A.mul_mem (hiA s) hyA⟩
      simp [hpi, hy1, hs]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro C hC
    rw [happ C hC.isClosed.measurableSet, hpre C]
    exact ((hC.image hi).prod hK).image continuous_mul |>.measure_lt_top
  · intro b
    ext S hS
    rw [Measure.map_apply (measurable_const_mul b) hS, happ _ (measurable_const_mul b hS), happ S hS]
    have : p ⁻¹' ((fun x => b * x) ⁻¹' S) ∩ A = (fun g => i b * g) ⁻¹' (p ⁻¹' S ∩ A) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, hpi, SetLike.mem_coe]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, A.mul_mem (hiA b) h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := A.mul_mem (A.inv_mem (hiA b)) h2
        simpa using this
    rw [this, measure_preimage_mul]
  · intro U hU hne
    rw [happ U hU.measurableSet]
    obtain ⟨u, hu⟩ := hne
    exact (hU.preimage hp |>.inter hA).measure_ne_zero ν ⟨i u, by simp [hpi, hu], hiA u⟩
end GlobalTheory.ChainOnto
