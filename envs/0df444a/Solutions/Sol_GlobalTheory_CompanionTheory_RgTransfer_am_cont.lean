-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.am_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:11.154805+00:00
-- url     : https://prove2.me/submissions/d406d499-70b7-4216-b103-611c794458f0

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
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) :
    Continuous fun y : Q × K => am ρ c₀ π y.1 y.2 := by
  have h1 : Continuous fun q : Q => c₀ q :=
    continuousOn_iff_continuous_restrict.1 hL.par.ch.cont
  unfold am
  refine (h1.comp continuous_fst).smul ?_
  exact (hρ.comp (continuous_inv.comp continuous_snd)).clm_comp continuous_const
end GlobalTheory.CompanionTheory.RgTransfer
