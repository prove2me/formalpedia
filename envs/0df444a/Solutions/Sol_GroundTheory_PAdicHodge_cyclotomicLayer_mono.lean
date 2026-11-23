-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cyclotomicLayer_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:27.028946+00:00
-- url     : https://prove2.me/submissions/fb9764c0-d807-4730-821d-a811f90315cd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_mono


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
theorem _root_.solution : Monotone (cyclotomicLayer K) := fun _ _ h =>
  sup_le_sup_left (cycl_mono h) K
end GroundTheory.PAdicHodge
