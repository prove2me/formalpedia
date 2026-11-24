-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.ext_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:27:39.19711+00:00
-- url     : https://prove2.me/submissions/e41cd53f-34af-45bc-af36-c1c3dca29bc2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_qk_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_am_bound

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution [LocallyCompactSpace G] {T : Type} (hK : IsCompact (K : Set G))
    (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) (S : Set T)
    (F : T → G' → E →L[ℂ] fixSp K Q π c₀ ρ)
    (hb : ∀ g', ∃ U ∈ 𝓝 g', ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ U, ‖F t x‖ ≤ M) (g : G) :
    ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ t ∈ S, ∀ g' ∈ U, ‖ext hL ρ (F t) g'‖ ≤ M := by
  obtain ⟨C, hC, hCg⟩ := exists_compact_mem_nhds g
  refine ⟨C, hCg, ?_⟩
  set C₁ : Set G := (fun a : G × G => a.1 * a.2⁻¹) '' (C ×ˢ (K : Set G)) with hC₁
  have hC₁c : IsCompact C₁ :=
    (hC.prod hK).image (continuous_fst.mul continuous_snd.inv)
  have hCq : IsCompact ((↑) ⁻¹' C₁ : Set Q) :=
    hL.par.closed.isClosedEmbedding_subtypeVal.isCompact_preimage hC₁c
  have hC' : IsCompact (π '' ((↑) ⁻¹' C₁ : Set Q)) := hCq.image hL.contπ
  have hM : ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ π '' ((↑) ⁻¹' C₁ : Set Q), ‖F t x‖ ≤ M := by
    refine hC'.induction_on (p := fun s => ∃ M : ℝ, ∀ t ∈ S, ∀ x ∈ s, ‖F t x‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨0, fun _ _ _ h => absurd h (Set.notMem_empty _)⟩
    · rintro s u hsu ⟨M, hM⟩
      exact ⟨M, fun t ht x hx => hM t ht x (hsu hx)⟩
    · rintro s u ⟨M, hM⟩ ⟨N, hN⟩
      refine ⟨max M N, fun t ht x hx => ?_⟩
      rcases hx with hx | hx
      · exact (hM t ht x hx).trans (le_max_left _ _)
      · exact (hN t ht x hx).trans (le_max_right _ _)
    · intro x _
      obtain ⟨U, hU, M, hM⟩ := hb x
      exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, M, hM⟩
  obtain ⟨M, hM⟩ := hM
  obtain ⟨B, hB⟩ := am_bound hK hL hρ
  refine ⟨B * M, fun t ht g' hg' => ?_⟩
  have hq : (qOf hL g' : G) ∈ C₁ := by
    refine ⟨(g', kOf hL g'), ⟨hg', (kOf hL g').2⟩, ?_⟩
    exact mul_inv_eq_of_eq_mul (qk_spec hL g')
  have h2 := hM t ht (π (qOf hL g')) ⟨_, hq, rfl⟩
  have h1 := hB (qOf hL g') (kOf hL g')
  unfold ext
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
end GlobalTheory.CompanionTheory.RgTransfer
