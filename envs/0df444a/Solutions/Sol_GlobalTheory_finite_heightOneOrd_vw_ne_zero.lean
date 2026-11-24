-- Prove2me | solution 1 for GlobalTheory.finite_heightOneOrd_vw_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:13.449947+00:00
-- url     : https://prove2.me/submissions/a3253c07-a3e8-4e08-a202-135a1e330692

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_finite_height_eq_one_mem
import Theorems.Thm_GlobalTheory_heightOneOrd_vw_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
namespace GlobalTheory
theorem _root_.solution {x : K} (hx : x ≠ 0) :
    {p : PrimeSpectrum A |
      ∃ hp : p.asIdeal.height = 1, heightOneOrd_vw p.asIdeal hp x ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  refine ((finite_height_eq_one_mem ha).union (finite_height_eq_one_mem hb0)).subset ?_
  rintro p ⟨hp, h⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, hp, true_and, not_or] at hn
  apply h
  rw [heightOneOrd_vw_div _ _ (IsFractionRing.to_map_eq_zero_iff.not.mpr ha)
    (IsFractionRing.to_map_eq_zero_iff.not.mpr hb0), heightOneOrd_vw_algebraMap_of_notMem _ _ hn.1,
    heightOneOrd_vw_algebraMap_of_notMem _ _ hn.2, sub_zero]
end GlobalTheory
