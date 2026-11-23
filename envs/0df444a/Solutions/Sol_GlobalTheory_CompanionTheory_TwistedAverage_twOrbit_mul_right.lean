-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.twOrbit_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:52.412911+00:00
-- url     : https://prove2.me/submissions/cb81c485-4f66-4687-8b55-d8f047c29dc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemTwKerIffAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwistedAverage
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.TwistedAverage
theorem _root_.solution (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x : V)
    (t k : L) (hk : k ∈ stabKer ρ L θ x) : twOrbit ρ L θ x (t * k) = twOrbit ρ L θ x t := by
  obtain ⟨h1, h2⟩ := hk
  simp only [twOrbit]
  rw [map_mul, h2, mul_one, Subgroup.coe_mul, map_mul, Module.End.mul_apply, h1]
end GlobalTheory.CompanionTheory.TwistedAverage
