-- Prove2me | solution 1 for GroundTheory.PAdicHodge.le_span_singleton_of_forall_mem_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:19:35.789983+00:00
-- url     : https://prove2.me/submissions/3fa51780-2221-4cb2-a28f-03a675b30736

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a
import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {R : Type*} [CommRing R]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {π ξ : R} [IsAdicComplete (Ideal.span {π}) R]
    {J : Ideal R} (h : ∀ x ∈ J, ∃ a z, z ∈ J ∧ x = a * ξ + z * π) :
    J ≤ Ideal.span {ξ} :=
  _root_.P2M_UpperTheory_Reformulated_B_Yhc2_le_span_singleton_of_forall_mem_eq__73902d423e3a h
end GroundTheory.PAdicHodge
