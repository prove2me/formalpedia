-- Prove2me | solution 1 for GroundTheory.PAdicHodge.gal_mem_cyclotomicLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:03.763225+00:00
-- url     : https://prove2.me/submissions/1e652c9e-ba79-4b8e-b72a-0ed91f1ce2ac

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_map_mem_cyclotomicLimit


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
theorem _root_.solution (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy
end GroundTheory.PAdicHodge
