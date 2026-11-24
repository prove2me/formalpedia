-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.transl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:39.882944+00:00
-- url     : https://prove2.me/submissions/0c010c50-6ab1-44a8-8423-9519fc49a6f8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_measurable_transl_fun

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
theorem _root_.solution (M : Subgroup G) (η : Measure M) (q x : G) :
    transl M η (q * x) = (transl M η x).map (fun y => q * y) := by
  unfold transl
  rw [Measure.map_map (measurable_const_mul _) (measurable_transl_fun M x)]
  congr 1
  ext y
  simp [mul_assoc]
end GlobalTheory.CompanionTheory.HaarPK
