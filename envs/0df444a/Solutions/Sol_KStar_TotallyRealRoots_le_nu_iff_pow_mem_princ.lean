-- Prove2me | solution 1 for KStar.TotallyRealRoots.le_nu_iff_pow_mem_princ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:39.255123+00:00
-- url     : https://prove2.me/submissions/78b63d86-8e8b-4685-81bb-86d6ba94b2b6

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Theorems.Thm_KStar_TotallyRealRoots_mem_princ
import Theorems.Thm_KStar_TotallyRealRoots_le_nu_iff

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
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, u ^ tr ∈ princ l n := by
  rw [le_nu_iff]
  simp only [mem_princ, Units.val_pow_eq_pow_val]
end KStar.TotallyRealRoots
