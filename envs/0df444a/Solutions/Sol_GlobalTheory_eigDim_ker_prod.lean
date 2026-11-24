-- Prove2me | solution 1 for GlobalTheory.eigDim_ker_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:44:50.813298+00:00
-- url     : https://prove2.me/submissions/27d263c8-e0af-4523-a42d-c217b0d5e8e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
import Theorems.Thm_GlobalTheory_eigDim_ker_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (s : Finset K) :
    Module.finrank K (LinearMap.ker (aeval T (∏ z ∈ s, (X - C z)))) =
      ∑ z ∈ s, Module.finrank K (LinearMap.ker (aeval T (X - C z))) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, map_one, Module.End.one_eq_id, LinearMap.ker_id]
    simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, eigDim_ker_mul T, ih]
    refine IsCoprime.prod_right fun z hz => ?_
    refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ?_).isUnit
    rintro rfl
    exact ha hz
end GlobalTheory
