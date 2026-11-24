-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.TubeGood_chg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:16.346973+00:00
-- url     : https://prove2.me/submissions/b6e1d13b-5d28-47c1-862a-1b2eaae30575

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_aff_re
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_continuous_chg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_continuous_chgR
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_tube_chg
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_lineHol_chg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    TubeGood (fun l g => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l) g) (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) := by
  refine ⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩
  · have hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2) :=
      ((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd
    refine hF.cont.comp hc.continuousOn ?_
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact ⟨mem_tube_chg.1 hl, Set.mem_univ _⟩
  · intro C hC hCc g
    obtain ⟨U, hU, M, hM⟩ := hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C)
      (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g
    refine ⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩
    have : (l.1.re, l.2.re) ∈ C := hl
    refine ⟨_, this, ?_⟩
    simp only [chg, chgR, aff_re]
end GlobalTheory.CompanionTheory.RgEisGal
