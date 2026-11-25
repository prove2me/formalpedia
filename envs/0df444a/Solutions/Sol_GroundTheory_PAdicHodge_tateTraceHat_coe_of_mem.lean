-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tateTraceHat_coe_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:47.028805+00:00
-- url     : https://prove2.me/submissions/8549ef79-581b-4f9c-8e29-e5be1a7862a1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_tateTrace_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_tateTrace_add_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_norm_tateTrace_le_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_le_cyclotomicLimit
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_coe_of_mem


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
open IntermediateField Module Set
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]
variable {K}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha
end GroundTheory.PAdicHodge
