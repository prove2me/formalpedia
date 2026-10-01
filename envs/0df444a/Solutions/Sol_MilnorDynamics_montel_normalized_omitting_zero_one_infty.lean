-- Prove2me | solution 1 for MilnorDynamics.montel_normalized_omitting_zero_one_infty
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T21:40:25.99196+00:00
-- url     : https://prove2.me/submissions/21de7274-c710-45ca-a523-60ca5f2e550c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_planar_part_of_sphere_omitting
import Theorems.Thm_MilnorDynamics_tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
import Theorems.Thm_MilnorDynamics_locally_bounded_holomorphic_subseq_locally_uniform
import Theorems.Thm_MilnorDynamics_either_limit_avoids_or_diverges
import Theorems.Thm_MilnorDynamics_not_locally_bounded_diverges
import Theorems.Thm_MilnorDynamics_diverging_subseq_tendsto_puncture

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Montel's theorem in normalised form, reduced to the published planar
pipeline: the sphere-to-plane bridge, the planar Arzela-Ascoli extraction child,
the Hurwitz-type limit child, the escape child, the proved Lemma 3.5, and the
Euclidean-to-chordal transport lemma. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧
      ∀ z ∈ U, f z ≠ ((0 : ℂ) : OnePoint ℂ) ∧ f z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ f z ≠ ∞) :
    IsNormalFamily U 𝓕 := by
  intro u hu
  have hpl : ∀ n, ∃ ĝ : ℂ → ℂ, DifferentiableOn ℂ ĝ U ∧ MapsTo ĝ U ({0, 1}ᶜ : Set ℂ) ∧
      ∀ z ∈ U, ((ĝ z : ℂ) : OnePoint ℂ) = u n z :=
    fun n => planar_part_of_sphere_omitting U (u n) (h𝓕 (u n) (hu n)).1 (h𝓕 (u n) (hu n)).2
  choose ĝ hĝ using hpl
  have hĝd : ∀ n, DifferentiableOn ℂ (ĝ n) U := fun n => (hĝ n).1
  have hĝm : ∀ n, MapsTo (ĝ n) U ({0, 1}ᶜ : Set ℂ) := fun n => (hĝ n).2.1
  have hĝe : ∀ n, ∀ z ∈ U, ((ĝ n z : ℂ) : OnePoint ℂ) = u n z := fun n => (hĝ n).2.2
  by_cases hbdd : ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖ĝ n z‖ ≤ M
  · obtain ⟨φ, hφ, g, hg, hcv⟩ :=
      locally_bounded_holomorphic_subseq_locally_uniform U hU ĝ (fun n => hĝd n) hbdd
    rcases either_limit_avoids_or_diverges U hU hUc (fun n => ĝ (φ n))
      (fun n => ⟨hĝd (φ n), hĝm (φ n)⟩) g hg hcv with hmap | hdiv
    · refine ⟨φ, hφ, fun z => ((g z : ℂ) : OnePoint ℂ), ?_, ?_⟩
      · exact OnePoint.continuous_coe.comp_continuousOn' hg
      · intro K hKU hK ε hε
        filter_upwards [tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly U hU
          (fun n => ĝ (φ n)) g hcv K hKU hK ε hε] with n hn
        intro x hx
        simpa [hĝe (φ n) x (hKU hx)] using hn x hx
    · obtain ⟨ψ, hψ, c, _hc, hcv'⟩ :=
        diverging_subseq_tendsto_puncture U hU hUc (fun n => ĝ (φ n))
          (fun n => ⟨hĝd (φ n), hĝm (φ n)⟩) hdiv
      refine ⟨φ ∘ ψ, hφ.comp hψ, fun _ => c, continuousOn_const, ?_⟩
      intro K hKU hK ε hε
      filter_upwards [hcv' K hKU hK ε hε] with n hn
      intro x hx
      simpa [hĝe (φ (ψ n)) x (hKU hx)] using hn x hx
  · have hKb : ∃ K ⊆ U, IsCompact K ∧ ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖ĝ n z‖ ≤ M) := by
      by_contra hcon
      exact hbdd fun K hKU hK => by
        by_contra hne
        exact hcon ⟨K, hKU, hK, hne⟩
    obtain ⟨K, hKU, hK, hne⟩ := hKb
    have hdiv := not_locally_bounded_diverges U hU hUc ĝ (fun n => ⟨hĝd n, hĝm n⟩)
      ⟨K, hKU, hK, hne⟩
    obtain ⟨φ, hφ, c, _hc, hcv⟩ :=
      diverging_subseq_tendsto_puncture U hU hUc ĝ (fun n => ⟨hĝd n, hĝm n⟩) hdiv
    refine ⟨φ, hφ, fun _ => c, continuousOn_const, ?_⟩
    intro K' hK'U hK' ε hε
    filter_upwards [hcv K' hK'U hK' ε hε] with n hn
    intro x hx
    simpa [hĝe (φ n) x (hK'U hx)] using hn x hx
