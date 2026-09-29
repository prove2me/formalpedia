-- Prove2me | solution 1 for MeasureTheory.Measure.map_eq_self_of_involutive_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/728fddf7-1a15-584e-989f-49b961ec35da

import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure

open MeasureTheory

namespace P2mInvolutiveHaar

p2m_open "MeasureTheory Measure MeasureTheory.Measure"

lemma nnreal_eq_one_of_mul_self_eq_one {c : NNReal} (h : c * c = 1) : c = 1 := by
  have h2 : c ^ 2 = 1 := by rw [pow_two]; exact h
  exact (pow_eq_one_iff_of_nonneg (show (0 : NNReal) ≤ c from bot_le) two_ne_zero).mp h2

lemma haarScalarFactor_congr_left
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {μ₁ μ₂ : Measure G} (ν : Measure G) [ν.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts μ₁] [μ₁.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ₂] [μ₂.IsMulLeftInvariant]
    (h : μ₁ = μ₂) : μ₁.haarScalarFactor ν = μ₂.haarScalarFactor ν := by
  subst h
  rfl

theorem map_eq_self_of_continuousMulEquiv_involutive
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G ≃ₜ* G) (hφinv : ∀ g : G, φ (φ g) = g) :
    Measure.map φ μ = μ := by

  have hmeas : Measurable (φ : G → G) := (map_continuous φ).measurable
  have hmm : Measure.map φ (Measure.map φ μ) = μ := by
    rw [Measure.map_map hmeas hmeas]
    have hcomp : ((φ : G → G) ∘ (φ : G → G)) = id := funext fun g => hφinv g
    rw [hcomp, Measure.map_id]

  set c : NNReal := (Measure.map φ μ).haarScalarFactor μ with hc
  have h1 : μ.haarScalarFactor (Measure.map φ μ) = c := by
    rw [hc, ← haarScalarFactor_map (Measure.map φ μ) μ φ]
    exact (haarScalarFactor_congr_left (Measure.map φ μ) hmm).symm
  have h2 : c * c = 1 := by
    have h := haarScalarFactor_eq_mul μ (Measure.map φ μ) μ
    rw [haarScalarFactor_self, h1] at h
    exact h.symm
  have h3 : c = 1 := nnreal_eq_one_of_mul_self_eq_one h2
  have key := isMulLeftInvariant_eq_smul (Measure.map φ μ) μ
  rw [← hc, h3, one_smul] at key
  exact key

end P2mInvolutiveHaar

open MeasureTheory

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (θ : G ≃* G) (hθ : Continuous θ) (hθinv : ∀ g : G, θ (θ g) = g) :
    Measure.map θ μ = μ := by

  have hsymm : Continuous θ.symm := by
    have h : (θ.symm : G → G) = θ := funext fun g => θ.symm_apply_eq.mpr (hθinv g).symm
    rw [h]; exact hθ

  let φ : G ≃ₜ* G := ⟨θ, hθ, hsymm⟩
  have hφ : ((φ : G ≃ₜ* G) : G → G) = θ := rfl
  have key := P2mInvolutiveHaar.map_eq_self_of_continuousMulEquiv_involutive μ φ
    (fun g => by rw [hφ]; exact hθinv g)
  rw [hφ] at key
  exact key

end S_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure
end P2MW
export P2MW.S_MeasureTheory_Measure_map_eq_self_of_involutive_of_isHaarMeasure (solution)
