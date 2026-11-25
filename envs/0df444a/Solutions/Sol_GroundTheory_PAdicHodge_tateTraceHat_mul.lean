-- Prove2me | solution 1 for GroundTheory.PAdicHodge.tateTraceHat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:49.686339+00:00
-- url     : https://prove2.me/submissions/ee4436dc-cc6a-4338-a725-48a2d4436652

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_tateTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_tateTrace_add_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_norm_tateTrace_le_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_le_cyclotomicLimit
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_mul


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
theorem _root_.solution {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx
end GroundTheory.PAdicHodge
