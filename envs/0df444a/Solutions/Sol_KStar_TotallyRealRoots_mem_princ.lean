-- Prove2me | solution 1 for KStar.TotallyRealRoots.mem_princ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:32.604211+00:00
-- url     : https://prove2.me/submissions/f086e8bd-9689-4747-ae98-f5c24c454ad4

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
theorem _root_.solution {a : ℕ} {u : ℤ_[l]ˣ} : u ∈ princ l a ↔ (l : ℤ_[l]) ^ a ∣ (u : ℤ_[l]) - 1 := by
  rw [princ, MonoidHom.mem_ker, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero, Units.ext_iff]
  simp [redPow]
end KStar.TotallyRealRoots
