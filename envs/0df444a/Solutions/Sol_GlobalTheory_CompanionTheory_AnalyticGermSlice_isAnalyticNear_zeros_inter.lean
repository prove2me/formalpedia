-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticGermSlice.isAnalyticNear_zeros_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:28.902149+00:00
-- url     : https://prove2.me/submissions/08b8a661-5870-4faf-9077-feb7ee4d964e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticGermFiniteProjection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticGermSlice
namespace GlobalTheory.CompanionTheory.AnalyticGermSlice
theorem _root_.solution {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ}
    (hX : IsAnalyticNear X w) {m : ℕ} (g : Fin m → (σ → ℂ) → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) Set.univ) :
    IsAnalyticNear {z | z ∈ X ∧ ∀ i, g i z = 0} w := by
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  refine ⟨N, k + m, Fin.append f g, hN, hwN, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left j => rw [Fin.append_left]; exact hf j
    | right j => rw [Fin.append_right]; exact (hg j).mono (Set.subset_univ N)
  · ext z
    have hz := Set.ext_iff.1 hXN z
    constructor
    · rintro ⟨⟨hzX, hg0⟩, hzN⟩
      refine ⟨hzN, (Fin.forall_fin_add _).2 ⟨fun j => ?_, fun j => ?_⟩⟩
      · rw [Fin.append_left]; exact (hz.1 ⟨hzX, hzN⟩).2 j
      · rw [Fin.append_right]; exact hg0 j
    · rintro ⟨hzN, hall⟩
      have h2 := (Fin.forall_fin_add _).1 hall
      refine ⟨⟨(hz.2 ⟨hzN, fun j => ?_⟩).1, fun j => ?_⟩, hzN⟩
      · have := h2.1 j
        rwa [Fin.append_left] at this
      · have := h2.2 j
        rwa [Fin.append_right] at this
end GlobalTheory.CompanionTheory.AnalyticGermSlice
