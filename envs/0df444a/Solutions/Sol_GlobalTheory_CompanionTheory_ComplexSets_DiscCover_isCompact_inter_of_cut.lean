-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.DiscCover.isCompact_inter_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:23.137811+00:00
-- url     : https://prove2.me/submissions/f9c6da2d-c53a-48f9-8e73-75f9f418b13a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedProperCountConstant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProjectionPushforward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets GlobalTheory.CompanionTheory.ComplexSets.DiscCover
open Metric
namespace GlobalTheory.CompanionTheory.ComplexSets.DiscCover
theorem _root_.solution {σ : Type} [Fintype σ] {Y C Nn : Set (σ → ℂ)} {k : ℕ}
    {f : Fin k → (σ → ℂ) → ℂ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) Nn)
    (hY : Y ∩ Nn = {z | z ∈ Nn ∧ ∀ i, f i z = 0}) (hC : IsCompact C) (hsub : C ⊆ Nn) :
    IsCompact (Y ∩ C) := by
  have hcont : ContinuousOn (fun z i => f i z) C :=
    continuousOn_pi.2 fun i => (hf i).continuousOn.mono hsub
  have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := (0 : Fin k → ℂ)))
  have heq : Y ∩ C = C ∩ (fun z i => f i z) ⁻¹' {(0 : Fin k → ℂ)} := by
    ext z
    constructor
    · rintro ⟨hzY, hzC⟩
      have h : z ∈ Y ∩ Nn := ⟨hzY, hsub hzC⟩
      rw [hY] at h
      exact ⟨hzC, funext h.2⟩
    · rintro ⟨hzC, hz⟩
      have h : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨hsub hzC, fun i => congrFun hz i⟩
      rw [← hY] at h
      exact ⟨h.1, hzC⟩
  rw [heq]
  exact hC.of_isClosed_subset hcl Set.inter_subset_left
end GlobalTheory.CompanionTheory.ComplexSets.DiscCover
