-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_cyclotomicCompletion_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:30.372376+00:00
-- url     : https://prove2.me/submissions/6f5f766d-e0d2-4443-a367-0e97e6fb6faf

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_ExistsGalFixCyclotomicLayerCycloCharNeOne
import Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_closedSubgroup_eq_closure


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
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x : ℂ_[p]}
    (hx : ∀ σ ∈ cyclotomicLimitGal K, σ • x = x) : x ∈ cyclotomicCompletion K := by
  have h := fixedPoints_closedSubgroup_eq_closure (cyclotomicLimitGal K)
    (InfiniteGalois.fixingSubgroup_isClosed _)
  have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ cyclotomicLimitGal K, σ • x = x} := hx
  rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
  exact hx'
end GroundTheory.PAdicHodge
