-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.am_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:10.260226+00:00
-- url     : https://prove2.me/submissions/88c7f7d0-274b-4f60-ae89-9438b763ef53

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
theorem _root_.solution (hK : IsCompact (K : Set G)) (hL : IsLevi Γ K Q Γ' K' π ι c₀)
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) : ∃ B : ℝ, ∀ (q : Q) (k : K), ‖am ρ c₀ π q k‖ ≤ B := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  refine ⟨B * ‖(fixSp K Q π c₀ ρ).subtypeL‖, fun q k => ?_⟩
  unfold am
  refine (norm_smul_le _ _).trans ?_
  rw [hL.par.ch.norm q q.2, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hB _ (Set.mem_univ _)) (norm_nonneg _)
end GlobalTheory.CompanionTheory.RgTransfer
