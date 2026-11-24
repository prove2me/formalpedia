-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.exists_equation_not_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:28.428038+00:00
-- url     : https://prove2.me/submissions/fb03273c-7eb2-4cfa-a0f7-f36df994ffea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
variable {σ : Type} [Fintype σ]
namespace GlobalTheory.CompanionTheory.ComplexSets
theorem _root_.solution {Y Z : Set (σ → ℂ)} {w : σ → ℂ} (hZ : IsAnalyticNear Z w)
    (hYZ : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → z ∈ Z) :
    ∃ φ : (σ → ℂ) → ℂ, AnalyticAt ℂ φ w ∧ (∀ᶠ z in 𝓝 w, z ∈ Z → φ z = 0) ∧
      ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 := by
  obtain ⟨N, k, f, hN, hwN, hf, hZN⟩ := hZ
  by_contra hcon
  push_neg at hcon
  apply hYZ
  have hall : ∀ i, ∀ᶠ z in 𝓝 w, z ∈ Y → f i z = 0 := by
    intro i
    apply hcon (f i) (hf i w hwN)
    filter_upwards [hN.mem_nhds hwN] with z hzN hzZ
    have hz : z ∈ Z ∩ N := ⟨hzZ, hzN⟩
    rw [hZN] at hz
    exact hz.2 i
  have hall' : ∀ᶠ z in 𝓝 w, ∀ i, z ∈ Y → f i z = 0 := Filter.eventually_all.mpr hall
  filter_upwards [hall', hN.mem_nhds hwN] with z hz hzN hzY
  have hz' : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
  rw [← hZN] at hz'
  exact hz'.1
end GlobalTheory.CompanionTheory.ComplexSets
