-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_cycl_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:15.625829+00:00
-- url     : https://prove2.me/submissions/51976b14-8f42-4a37-b4ce-4b20b4920871

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_finrank_linearDisjoint
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_eq_of_finrank_sup


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
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m)
    {z : PadicAlgCl p} (hz : z ∈ cyclotomicLayer K n) :
    normTrace (cycl p m) z = normTrace (cycl p n) z := by
  refine normTrace_eq_of_finrank_sup (cycl_le_cyclotomicLayer K n) (cycl_mono hnm) ?_ hz
  rw [cyclotomicLayer_sup_cycl K hnm]
  exact finrank_linearDisjoint K hn hnm
end GroundTheory.PAdicHodge
