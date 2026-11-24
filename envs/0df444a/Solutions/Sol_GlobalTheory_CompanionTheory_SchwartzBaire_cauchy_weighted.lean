-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SchwartzBaire.cauchy_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:13.381248+00:00
-- url     : https://prove2.me/submissions/ed9c7e49-56c6-4e19-8b57-973e5b289d41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SchwartzBaire_iteratedFDeriv_sub_apply__4bfc50ada7a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff Topology Uniformity
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SchwartzBaire
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory.CompanionTheory.SchwartzBaire
theorem _root_.solution (f : ℕ → 𝓢(E, F)) (hf : CauchySeq f) (k l : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (f m) x - iteratedFDeriv ℝ l (f m') x‖ ≤ ε := by
  have h0 := hf.tendsto_uniformity
  rw [uniformity_eq_comap_nhds_zero 𝓢(E, F), tendsto_comap_iff] at h0
  have h1 := ((schwartz_withSeminorms ℝ E F).tendsto_nhds _ 0).1 h0 (k, l) ε hε
  obtain ⟨⟨N₁, N₂⟩, hN⟩ := eventually_atTop.1 h1
  refine ⟨max N₁ N₂, fun m hm m' hm' x => ?_⟩
  have hmm := hN (m', m) ⟨le_trans (le_max_left _ _) hm', le_trans (le_max_right _ _) hm⟩
  simp only [Function.comp_apply, Prod.map_apply, sub_zero] at hmm
  rw [← iteratedFDeriv_sub_apply']
  exact (SchwartzMap.le_seminorm ℝ k l (f m - f m') x).trans hmm.le
end GlobalTheory.CompanionTheory.SchwartzBaire
