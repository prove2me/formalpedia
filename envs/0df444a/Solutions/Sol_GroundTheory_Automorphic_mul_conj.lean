-- Prove2me | solution 1 for GroundTheory.Automorphic.mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:25.280039+00:00
-- url     : https://prove2.me/submissions/e0fe9c40-6270-4ef5-97f5-dd420d60cb12

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Theorems.Thm_GroundTheory_Automorphic_norm_eq_of_not_mem
import Theorems.Thm_GroundTheory_Automorphic_conj_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]
variable {F E}
variable [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution (x : E) : x * conj F E x = algebraMap F E (Algebra.norm F x) := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conj_algebraMap, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow, sq]
  · have hsq := sq_eq_of_not_mem hx
    rw [conj_apply, trace_eq_of_not_mem hx, norm_eq_of_not_mem hx, map_neg]
    linear_combination (-1 : E) * hsq
end GroundTheory.Automorphic
