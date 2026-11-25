-- Prove2me | solution 1 for GroundTheory.Automorphic.IsCyclicVector.exists_aeval_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:17.3668+00:00
-- url     : https://prove2.me/submissions/96510af1-858f-4a86-aadb-d14a1dae898c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Theorems.Thm_GroundTheory_Automorphic_cyclicBasis_apply
import Theorems.Thm_GroundTheory_Automorphic_aeval_C_mul_X_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Polynomial Module Matrix
variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']
variable {f : Module.End E V} {v : V}
namespace GroundTheory.Automorphic
namespace IsCyclicVector
theorem _root_.solution (hv : IsCyclicVector f v) (x : V) :
    ∃ p : E[X], aeval f p v = x := by
  refine ⟨∑ k : Fin (finrank E V), C ((cyclicBasis hv).repr x k) * X ^ (k : ℕ), ?_⟩
  conv_rhs => rw [← (cyclicBasis hv).sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [aeval_C_mul_X_pow_apply, cyclicBasis_apply]
end IsCyclicVector
end GroundTheory.Automorphic
