-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:23.881089+00:00
-- url     : https://prove2.me/submissions/fcca5e6d-83f7-4734-b2af-a49d22e1b929

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermMeetOverHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeetOverHypersurfaceOfGerm
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_exists_hypersurface_of_monic_relation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
namespace GlobalTheory.CompanionTheory.ComplexSets
theorem _root_.solution
    (H : FiniteFibreGermIntegral.Statement) : IrreducibleGermMeetOverHypersurface.Statement := by
  intro σ _ Y Z w d A hY hirr hfib hZ hnot
  obtain ⟨N₀, k, f, hN₀, hwN₀, hf, hZN⟩ := hZ
  have hex : ∃ m, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → f m z = 0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    filter_upwards [eventually_all.2 hcon, hN₀.mem_nhds hwN₀] with z hz hzN hzY
    have hmem : z ∈ {z | z ∈ N₀ ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
    rw [← hZN] at hmem
    exact hmem.1
  obtain ⟨m, hm⟩ := hex
  have hφ : AnalyticAt ℂ (f m) w := hf m w hwN₀
  obtain ⟨N, a, ha, hrel⟩ := H σ Y w d A hY hfib (f m) hφ
  obtain ⟨e, he, hne, hz⟩ := exists_hypersurface_of_monic_relation A hirr hφ hm N a ha hrel
  refine ⟨e, he, hne, ?_⟩
  filter_upwards [hz, hN₀.mem_nhds hwN₀] with z hz' hzN hzY hzZ
  have hmem : z ∈ Z ∩ N₀ := ⟨hzZ, hzN⟩
  rw [hZN] at hmem
  exact hz' hzY (hmem.2 m)
end GlobalTheory.CompanionTheory.ComplexSets
