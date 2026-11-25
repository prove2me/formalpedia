-- Prove2me | solution 1 for GroundTheory.Automorphic.trace_comp_comm_of_isHilbertSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:44:57.89812+00:00
-- url     : https://prove2.me/submissions/a8e55dab-dec8-4614-87b3-b31193b8a72f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Theorems.Thm_GroundTheory_Automorphic_hasSum_inner_comp_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace GroundTheory.Automorphic
theorem _root_.solution {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : trace (A.comp B) = trace (B.comp A) :=
  (hasSum_inner_comp_comm (stdHilbertBasis ℂ H) (stdHilbertBasis ℂ H) hA hB).tsum_eq
end GroundTheory.Automorphic
