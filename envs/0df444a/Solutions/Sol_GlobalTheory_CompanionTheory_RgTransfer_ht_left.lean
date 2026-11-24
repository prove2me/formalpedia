-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.ht_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:33.31617+00:00
-- url     : https://prove2.me/submissions/1fd133cc-3ec1-4642-baec-9e6e45b6a9ba

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe

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
variable {A A' B B' : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup A']
  [NormedSpace ℂ A'] [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup B']
  [NormedSpace ℂ B']
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution {P : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) {γ : G} (hγ : γ ∈ Γ) (hγP : γ ∈ P)
    (x : G) : η (γ * x) = η x := by
  rw [h.left γ hγP, h.rat γ hγ hγP, zero_add]
end GlobalTheory.CompanionTheory.RgTransfer
