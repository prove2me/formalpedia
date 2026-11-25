-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.resRep_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:00.379297+00:00
-- url     : https://prove2.me/submissions/3840f6e0-f06c-45d2-b10c-0b5f799fb82c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_RgTransfer_k__cont_339454cbab40

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
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution [FiniteDimensional ℂ W] (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) : Continuous (resRep hL ρ) := by
  rw [continuous_clm_apply]
  intro v
  refine Continuous.subtype_mk ?_ _
  have : Continuous fun m : K' => (ρ (kι hL m)) (v : W) :=
    (continuous_eval_const (v : W)).comp (hρ.comp (kι_cont hL))
  exact this
end GlobalTheory.CompanionTheory.RgTransfer
