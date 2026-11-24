-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisSec.sec_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:31.495575+00:00
-- url     : https://prove2.me/submissions/e95cf7eb-a681-4715-b914-169a8730285b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_Iwa
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionLawHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisSec
variable {G : Type} [Group G] [TopologicalSpace G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisSec
theorem _root_.solution {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)}
    (hK : IsCompact (K : Set G)) (hρ : Continuous ρ) (hpar : IsPar Γ K P c) :
    ∃ M : ℝ, ∀ g (w : W), ‖sec K P c ρ g w‖ ≤ M * ‖w‖ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M, hM⟩ := (isCompact_range hρ).isBounded.exists_norm_le
  refine ⟨M, fun g w => ?_⟩
  obtain ⟨p, hp, k, hk, rfl⟩ := hpar.iwa g
  have h : ∃ k' : K, (p * k) * (k' : G)⁻¹ ∈ P := ⟨⟨k, hk⟩, by simpa using hp⟩
  rw [sec, dif_pos h, ContinuousLinearMap.smul_apply, norm_smul, hpar.ch.norm _ h.choose_spec,
    one_mul]
  exact ((ρ _).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hM _ ⟨_, rfl⟩) (norm_nonneg _))
end GlobalTheory.CompanionTheory.RgEisSec
