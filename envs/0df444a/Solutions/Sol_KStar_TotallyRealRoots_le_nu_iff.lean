-- Prove2me | solution 1 for KStar.TotallyRealRoots.le_nu_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:31.328613+00:00
-- url     : https://prove2.me/submissions/3e435425-fe92-4b79-864f-5b3f0e1f3ff6

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
theorem _root_.solution {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} :
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, (l : ℤ_[l]) ^ n ∣ (u : ℤ_[l]) ^ tr - 1 := by
  rw [nu, le_nuStar_iff, Set.forall_mem_image]
  rfl
end KStar.TotallyRealRoots
