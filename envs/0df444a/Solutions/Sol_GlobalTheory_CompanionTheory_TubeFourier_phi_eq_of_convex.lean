-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:39:01.500545+00:00
-- url     : https://prove2.me/submissions/39e99a7f-bc4f-460f-90c4-a65663eaec06

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformHorizontalInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformVerticalInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformIndependentOfBase
import Theorems.Thm_GlobalTheory_T_tube_transform_horizontal_invariance
import Theorems.Thm_GlobalTheory_T_tube_transform_vertical_invariance


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω →
    ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  intro X _ _ _ Ω G hΩ hconv hG x hx x' hx' t
  have hhor : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (s, c) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (a, c) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (b, c) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hver : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (c, s) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (c, a) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (c, b) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hf : IsLocallyConstant (fun p : Ω => GlobalTheory.CompanionTheory.TubeFourier.phi G (p : ℝ × ℝ) t) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨⟨p₁, p₂⟩, hp⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ (p₁, p₂) hp
    have hmem : {q : Ω | (q : ℝ × ℝ) ∈ Metric.ball (p₁, p₂) ε} ∈ 𝓝 (⟨(p₁, p₂), hp⟩ : Ω) :=
      continuousAt_subtype_val.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem]
    rintro ⟨⟨q₁, q₂⟩, hq⟩ hqball
    have hd : dist q₁ p₁ < ε ∧ dist q₂ p₂ < ε := by
      have h' : dist (q₁, q₂) (p₁, p₂) < ε := hqball
      rwa [Prod.dist_eq, max_lt_iff] at h'
    obtain ⟨h₁, h₂⟩ := hd
    rw [Real.dist_eq] at h₁ h₂
    have hv : GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t := by
      refine hver p₂ q₂ q₁ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨h₁, lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₂⟩
    have hh : GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t := by
      refine hhor p₁ q₁ p₂ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_self, Real.dist_eq]
      exact ⟨lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₁, hε⟩
    show GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t
    rw [← hv, ← hh]
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hconv.isPreconnected
  exact hf.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ (⟨x, hx⟩ : Ω))
    (Set.mem_univ (⟨x', hx'⟩ : Ω))
end GlobalTheory.CompanionTheory.TubeFourier
