-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_pow_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:41.553453+00:00
-- url     : https://prove2.me/submissions/f8a3c351-e929-48bd-a427-19bdc135d673

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
variable {R : Type*} [CommRing R] [Finite R]
namespace GlobalTheory.NormMod
theorem _root_.solution (a : R) :
    ∃ k, 0 < k ∧ ∀ P : Ideal R, P.IsPrime → a ∉ P → a ^ k - 1 ∈ P := by
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a ^ n)
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact ⟨i, j, h', h⟩
    · exact ⟨j, i, h', h.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨k + 1, k.succ_pos, fun P hP ha => ?_⟩
  have : a ^ i * (a ^ (k + 1) - 1) ∈ P := by
    rw [show a ^ i * (a ^ (k + 1) - 1) = 0 by linear_combination -h]
    exact P.zero_mem
  exact (hP.mem_or_mem this).resolve_left fun h => ha (hP.mem_of_pow_mem _ h)
end GlobalTheory.NormMod
