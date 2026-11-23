-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.measurable_transl_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:20.242725+00:00
-- url     : https://prove2.me/submissions/bed0929c-d810-4cf3-a272-d44bf89bbacb

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HaarPK
theorem _root_.solution (M : Subgroup G) (x : G) : Measurable (fun m : M => x * (m : G)) :=
  measurable_subtype_coe.const_mul x
end GlobalTheory.CompanionTheory.HaarPK
