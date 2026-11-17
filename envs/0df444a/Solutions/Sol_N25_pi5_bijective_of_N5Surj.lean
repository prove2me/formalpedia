-- Prove2me | solution 1 for N25.pi5_bijective_of_N5Surj
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:42.926277+00:00
-- url     : https://prove2.me/submissions/2729de03-a463-48be-9daa-7bffa50cf345

import Mathlib
import Theorems.Thm_N25_pi5_injective
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
import Theorems.Thm_N25_LocalFive_bijective_of_injective_of_factor_nsmul_of_surjective_subgroup
import Definitions.Def_N25_LocalFiveArithmetic

noncomputable section

namespace N25

/-- Finite-index division makes the injective local isogeny onto. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN5 : N5Surj) : Function.Bijective pi5 := by
  apply LocalFive.bijective_of_injective_of_factor_nsmul_of_surjective_subgroup
    71 pi5 rho5 _ (pi5_injective K2) hN5
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  exact DFunLike.congr_fun (piEnd_comp_rhoEnd hPhi) (x : J)

end N25
