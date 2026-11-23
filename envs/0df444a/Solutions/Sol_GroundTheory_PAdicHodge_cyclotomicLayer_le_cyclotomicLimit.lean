-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclotomicLayer_le_cyclotomicLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:46.202636+00:00
-- url     : https://prove2.me/submissions/fb6bb6b3-a853-457b-b723-f2dff7b32df4

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) : cyclotomicLayer K n ≤ cyclotomicLimit K :=
  le_iSup (cyclotomicLayer K) n
end GroundTheory.PAdicHodge
