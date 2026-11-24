-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwistedAverage.twOrbit_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:55.198582+00:00
-- url     : https://prove2.me/submissions/12a52604-9c83-4788-bd33-dac0133fbeb6

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
theorem _root_.solution (ρ : Representation ℂ G V) (L : Subgroup G) (θ : L →* ℂˣ) (c : ℂ) (x : V)
    (t : L) : twOrbit ρ L θ (c • x) t = c • twOrbit ρ L θ x t := by
  simp only [twOrbit, map_smul]
  rw [smul_comm]
end GlobalTheory.CompanionTheory.TwistedAverage
