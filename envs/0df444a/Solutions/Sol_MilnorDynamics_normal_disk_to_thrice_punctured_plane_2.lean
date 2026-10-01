-- Prove2me | solution 2 for MilnorDynamics.normal_disk_to_thrice_punctured_plane
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T18:40:45.343969+00:00
-- url     : https://prove2.me/submissions/630056d7-6473-47b7-9455-7cabd0b298ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_either_limit_avoids_or_diverges
import Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
import Theorems.Thm_MilnorDynamics_not_locally_bounded_subseq_diverges

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 6: the corrected reduction for Corollary 3.3.

Two changes against variant 3, both forced by counterexamples found this session:

* The **unbounded** branch no longer returns `φ = id`. It uses child
  `not_locally_bounded_subseq_diverges`, which returns an escaping subsequence.
  Demanding that the whole sequence escape is false: with
  `f (2m) = 4m / (2 + z)` and `f (2m+1) = 1/2 + z/4` on the disk the family is not
  locally bounded, yet every odd term still takes the value `1/2`.
* The **bounded** branch uses `locally_bounded_holomorphic_subseq_locally_uniform`
  rather than the continuous-map version, which is false: the bumps
  `z ↦ max (0, 1 - n ‖z‖)` are bounded on every compact and have no locally
  uniformly convergent subsequence.

`theorem solution` is top level, with the namespace opened outside it. -/
theorem solution (𝓕 : Set (ℂ → ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      MapsTo f (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) :
    IsNormalFamilyInto (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) 𝓕 := by
  intro f hf
  have hff : ∀ n, DifferentiableOn ℂ (f n) (Metric.ball 0 1) ∧
      MapsTo (f n) (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) :=
    fun n => h𝓕 (f n) (hf n)
  by_cases hesc : ∃ K ⊆ Metric.ball 0 1, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
  · obtain ⟨φ, hφ, hd⟩ :=
      MilnorDynamics.not_locally_bounded_subseq_diverges (Metric.ball 0 1)
        (Metric.isOpen_ball)
        (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1))
        f (fun n => hff n) hesc
    exact ⟨φ, hφ, Or.inr hd⟩
  · have hbdd : ∀ K ⊆ Metric.ball 0 1, IsCompact K →
        ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M := by
      intro K hKU hK
      by_contra hcon
      exact hesc ⟨K, hKU, hK, hcon⟩
    obtain ⟨φ, hφ, g, hg, hcv⟩ :=
      MilnorDynamics.locally_bounded_holomorphic_subseq_locally_uniform
        (Metric.ball 0 1) (Metric.isOpen_ball) f (fun n => (hff n).1) hbdd
    refine ⟨φ, hφ, ?_⟩
    rcases MilnorDynamics.either_limit_avoids_or_diverges (Metric.ball 0 1)
      (Metric.isOpen_ball)
      (Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)) (fun n => f (φ n))
      (fun n => hff (φ n)) g hg hcv with hm | hd
    · exact Or.inl ⟨g, hg, hm, hcv⟩
    · exact Or.inr hd
