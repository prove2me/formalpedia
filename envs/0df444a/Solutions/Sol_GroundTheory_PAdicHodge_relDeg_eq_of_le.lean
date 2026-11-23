-- Prove2me | solution 1 for GroundTheory.PAdicHodge.relDeg_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:45.235064+00:00
-- url     : https://prove2.me/submissions/1298a25a-473c-4320-bc85-ec849d98b7da

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower

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
theorem _root_.solution {m : ℕ} (h : stableIndex K ≤ m) : relDeg K m = relDeg K (stableIndex K) :=
  (Classical.choose_spec (exists_relDeg_stable K)).2 m h
end GroundTheory.PAdicHodge
