-- Prove2me | solution 1 for KStar.TotallyRealRoots.mem_levelGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:42.301745+00:00
-- url     : https://prove2.me/submissions/cb08a8ca-6199-4cf9-83ed-a3e0722c926c

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.TotallyRealRoots
variable (l : ℕ) [Fact l.Prime]
variable {l}
namespace KStar.TotallyRealRoots
theorem _root_.solution {N : ℕ} {H : Subgroup (ZMod N)ˣ} {u : ℤ_[l]ˣ} :
    u ∈ levelGroup l N H ↔
      ∃ h ∈ H, ZMod.unitsMap (Nat.ordProj_dvd N l) h = redPow l (N.factorization l) u := Iff.rfl
end KStar.TotallyRealRoots
