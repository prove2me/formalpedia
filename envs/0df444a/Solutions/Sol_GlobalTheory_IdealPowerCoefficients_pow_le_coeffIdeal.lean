-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.pow_le_coeffIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:56:12.588683+00:00
-- url     : https://prove2.me/submissions/1e6e2d15-9ff5-4894-9483-5d5594423a8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_mem_coeffIdeal
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_coeffIdeal_mul_le
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_le_coeffIdeal_one

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
theorem _root_.solution (I : Ideal R) (n : ℕ) :
    (Ideal.map C I ⊔ Ideal.span (Set.range X)) ^ n ≤ coeffIdeal (κ := κ) I n := by
  induction n with
  | zero =>
    intro f _
    rw [mem_coeffIdeal]
    intro e
    simp
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (le_coeffIdeal_one I)).trans (coeffIdeal_mul_le I n 1)
end GlobalTheory.IdealPowerCoefficients
