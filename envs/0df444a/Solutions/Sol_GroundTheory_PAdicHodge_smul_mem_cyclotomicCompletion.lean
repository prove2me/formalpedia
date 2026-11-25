-- Prove2me | solution 1 for GroundTheory.PAdicHodge.smul_mem_cyclotomicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:50.510804+00:00
-- url     : https://prove2.me/submissions/c62b9d17-2e31-4441-a5ec-df899bd1b640

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_gal_mem_cyclotomicLimit
import Theorems.Thm_GroundTheory_PAdicHodge_smul_mem_closureInCp


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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx
end GroundTheory.PAdicHodge
