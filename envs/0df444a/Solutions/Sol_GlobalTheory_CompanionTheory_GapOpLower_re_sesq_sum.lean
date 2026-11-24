-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GapOpLower.re_sesq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:33:20.542176+00:00
-- url     : https://prove2.me/submissions/b7f53609-843e-43c3-aab3-6bc7d4a60517

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCountFromHyperplanes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GapOpLower
open Finset
namespace GlobalTheory.CompanionTheory.GapOpLower
theorem _root_.solution {V ι : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (s t : Finset ι) (f : ι → V) :
    (B (∑ a ∈ s, f a) (∑ b ∈ t, f b)).re = ∑ a ∈ s, ∑ b ∈ t, (B (f a) (f b)).re := by
  simp only [map_sum, LinearMap.sum_apply, Complex.re_sum]
  rw [Finset.sum_comm]
end GlobalTheory.CompanionTheory.GapOpLower
