-- Prove2me | solution 1 for KStar.TotallyRealRoots.mem_twistInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:30.810165+00:00
-- url     : https://prove2.me/submissions/844cbeaa-24f2-4285-ac75-ca1798325ab8

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
theorem _root_.solution {A : Type*} [AddCommGroup A] [Module ℤ_[l] A] {U : Subgroup ℤ_[l]ˣ} {tr : ℕ}
    {x : A} : x ∈ twistInv l A U tr ↔ ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x := Iff.rfl
end KStar.TotallyRealRoots
