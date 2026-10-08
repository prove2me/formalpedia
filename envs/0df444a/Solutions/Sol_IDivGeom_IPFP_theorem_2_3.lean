-- Prove2me | solution 1 for IDivGeom.IPFP.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:22:59.694032+00:00
-- url     : https://prove2.me/submissions/1c631e12-1b2a-4fbb-b6af-d87d0badf3ac

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

open MeasureTheory InformationTheory IDivGeom.IPFP in
theorem solution {X : Type*} [MeasurableSpace X]
    (ℰ ℰ₁ : Set (Measure X)) (hℰ : ∀ P ∈ ℰ, IsProbabilityMeasure P)
    (h1 : ℰ₁ ⊆ ℰ) (hconv : IsConvexPD ℰ) (hconv1 : IsConvexPD ℰ₁)
    (R : Measure X) [IsProbabilityMeasure R] (Q Q₁ : Measure X)
    (hQ : IsIProjection R ℰ Q) (hQ1 : IsIProjection R ℰ₁ Q₁)
    (h17 : ∀ P ∈ ℰ, klDiv P R = klDiv P Q + klDiv Q R) :
    IsIProjection Q ℰ₁ Q₁ := by
  obtain ⟨hQ1mem, hQ1fin, hQ1min⟩ := hQ1
  obtain ⟨_, hQfin, _⟩ := hQ
  have e1 := h17 Q₁ (h1 hQ1mem)
  refine ⟨hQ1mem, ?_, ?_⟩
  · intro htop
    apply hQ1fin
    rw [e1, htop, top_add]
  · intro P hP
    have eP := h17 P (h1 hP)
    have hle := hQ1min P hP
    rw [e1, eP] at hle
    exact (ENNReal.add_le_add_iff_right hQfin).1 hle
