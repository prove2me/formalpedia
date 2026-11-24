-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.twOrbit_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:52.545882+00:00
-- url     : https://prove2.me/submissions/020f5bee-9fb9-44a3-808f-bad7643ec66d

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
theorem _root_.solution (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (x y : V) (t : L) :
    twOrbit ρ L θ (x + y) t = twOrbit ρ L θ x t + twOrbit ρ L θ y t := by
  simp only [twOrbit, map_add, smul_add]
end GlobalTheory.CompanionTheory.TwistedAverage
