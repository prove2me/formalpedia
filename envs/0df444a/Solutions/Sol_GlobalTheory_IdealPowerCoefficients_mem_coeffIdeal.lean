-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.mem_coeffIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:21.638296+00:00
-- url     : https://prove2.me/submissions/cc46f13d-0d98-463e-945e-21ae62c3ef5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}
namespace GlobalTheory.IdealPowerCoefficients
theorem _root_.solution {I : Ideal R} {n : ℕ} {f : MvPowerSeries κ R} :
    f ∈ coeffIdeal I n ↔ ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree) := Iff.rfl
end GlobalTheory.IdealPowerCoefficients
