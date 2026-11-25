-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cpTwistRep_invariants_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:47.781454+00:00
-- url     : https://prove2.me/submissions/cc9a7477-7d8c-47f6-9b55-720805a2d1be

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_eq_zero_of_forall_twistScalar_mul_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField UniformSpace
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {j : ℤ} (hj : j ≠ 0) : (cpTwistRep K j).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [ContRepresentation.mem_invariants] at hx
  exact (Submodule.mem_bot K).2 (eq_zero_of_forall_twistScalar_mul_smul_eq K hj hx)
end GroundTheory.PAdicHodge
