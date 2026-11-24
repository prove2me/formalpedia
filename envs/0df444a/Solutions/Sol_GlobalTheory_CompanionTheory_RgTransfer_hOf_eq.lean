-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.hOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:49:23.49824+00:00
-- url     : https://prove2.me/submissions/3040da11-a91d-40fa-93a8-15bccd94b29c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_ext_eq

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
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (ρ : K →* (W →L[ℂ] W)) {L' : Type}
    [NormedAddCommGroup L'] [NormedSpace ℂ L'] (e : A ≃L[ℂ] L')
    {H' : ℂ → G' → (L' →L[ℂ] fixSp K Q π c₀ ρ)}
    (hE : ∀ z (g : G') (k : K') (w : L'), H' z (g * k) w = resRep hL ρ k⁻¹ (H' z g w))
    (z : ℂ) (q : Q) (k : K) (w : A) :
    hOf hL ρ e H' z ((q : G) * k) w = am ρ c₀ π q k (H' z (π q) (e w)) := by
  have h := ext_eq hL ρ (F := fun g' => (H' z g').comp (e : A →L[ℂ] L'))
    (fun g m x => hE z g m (e x)) q k
  exact congrArg (fun T : A →L[ℂ] W => T w) h
end GlobalTheory.CompanionTheory.RgTransfer
