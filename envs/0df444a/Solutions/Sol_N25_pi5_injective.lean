-- Prove2me | solution 1 for N25.pi5_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:14.316021+00:00
-- url     : https://prove2.me/submissions/3d677cb8-4b46-4b72-9b9b-13b67e8ffd20

import Mathlib
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_N25_piEnd_eq_zero_of_fixedAtFive
import Definitions.Def_N25_LocalFiveArithmetic

noncomputable section

namespace N25

/-- The selected isogeny is injective on local fixed points. -/
theorem _root_.solution (K2 : K2Rows) : Function.Injective pi5 := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply piEnd_eq_zero_of_fixedAtFive K2
  · rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val h)
  · intro τ
    rw [smul_sub, x.property τ, y.property τ]

end N25
