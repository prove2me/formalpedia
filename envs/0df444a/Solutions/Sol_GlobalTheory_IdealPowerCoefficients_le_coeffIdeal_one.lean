-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.le_coeffIdeal_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:14.735918+00:00
-- url     : https://prove2.me/submissions/edde3ae6-5c33-4917-8c90-4268e69f0433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_mem_coeffIdeal

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
theorem _root_.solution (I : Ideal R) :
    Ideal.map C I ⊔ Ideal.span (Set.range X) ≤ coeffIdeal (κ := κ) I 1 := by
  classical
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, mem_coeffIdeal]
    intro e
    rw [coeff_C]
    split_ifs with h
    · subst h
      simpa using hi
    · exact Ideal.zero_mem _
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_coeffIdeal]
    intro e
    rw [coeff_X]
    split_ifs with h
    · subst h
      simp
    · exact Ideal.zero_mem _
end GlobalTheory.IdealPowerCoefficients
