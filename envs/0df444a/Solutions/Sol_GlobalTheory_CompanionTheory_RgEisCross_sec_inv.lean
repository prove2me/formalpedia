-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisCross.sec_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:01:33.756811+00:00
-- url     : https://prove2.me/submissions/b3f2e09a-ca0f-4382-950c-f4153c41a505

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicSeriesUniformTubeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionInvarianceCosetSumStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSeriesSummableShiftedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossingOfWallsAndHeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisCross
namespace GlobalTheory.CompanionTheory.RgEisCross
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {w : W} (hP : IsPar Γ K P c)
    (law : ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) :
    ∀ γ ∈ Γ, γ ∈ P → ∀ x, sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  intro γ hγ hγP x
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have h1 := law (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := law p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, hP.ch.mul γ hγP p hp, hP.ch.rat γ hγ hγP, one_mul]
end GlobalTheory.CompanionTheory.RgEisCross
