-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.not_eventually_prod_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:36.190927+00:00
-- url     : https://prove2.me/submissions/42d8c9cb-112a-4272-b976-56ab26ce43cd

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
theorem _root_.solution {ι : Type} {Y : Set (σ → ℂ)} {w : σ → ℂ}
    (hY : GermIrreducibleAt Y w) (φ : ι → (σ → ℂ) → ℂ) (s : Finset ι)
    (hφ : ∀ j ∈ s, AnalyticAt ℂ (φ j) w)
    (hne : ∀ j ∈ s, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ j z = 0) :
    ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → ∏ j ∈ s, φ j z = 0 := by
  classical
  obtain ⟨hwY, hirr⟩ := hY
  revert hφ hne
  refine Finset.induction_on s ?_ ?_
  · intro _ _ h
    have h0 := h.self_of_nhds hwY
    simp at h0
  · intro a s has ih hφ hne h
    simp_rw [Finset.prod_insert has] at h
    rcases hirr (φ a) (fun z => ∏ j ∈ s, φ j z) (hφ a (Finset.mem_insert_self a s))
        (by simpa only [Finset.prod_fn] using
          Finset.analyticAt_prod s fun j hj => hφ j (Finset.mem_insert_of_mem hj)) h with h1 | h1
    · exact hne a (Finset.mem_insert_self a s) h1
    · exact ih (fun j hj => hφ j (Finset.mem_insert_of_mem hj))
        (fun j hj => hne j (Finset.mem_insert_of_mem hj)) h1
end GlobalTheory.CompanionTheory.ComplexSets
