-- Prove2me | solution 1 for GroundTheory.PAdicHodge.finrank_linearDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:52.754497+00:00
-- url     : https://prove2.me/submissions/3411c81e-6c3c-4589-898f-2ec5954ee405

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_relDeg_eq_of_le

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
theorem _root_.solution {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) :
    finrank ℚ_[p] (cyclotomicLayer K m) * finrank ℚ_[p] (cycl p n) =
      finrank ℚ_[p] (cyclotomicLayer K n) * finrank ℚ_[p] (cycl p m) := by
  rw [finrank_cyclotomicLayer, finrank_cyclotomicLayer, relDeg_eq_of_le K hn,
    relDeg_eq_of_le K (hn.trans hnm)]
  ring
end GroundTheory.PAdicHodge
