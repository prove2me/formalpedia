-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.transl_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:41.129349+00:00
-- url     : https://prove2.me/submissions/71353420-79ed-4a12-baa2-39e85928a4d2

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
theorem _root_.solution (M : Subgroup G) (η : Measure M) [η.IsMulLeftInvariant] (x : G) {m : G} (hm : m ∈ M) :
    transl M η (x * m) = transl M η x := by
  unfold transl
  conv_rhs => rw [← map_mul_left_eq_self η ⟨m, hm⟩]
  rw [Measure.map_map (measurable_transl_fun M x) (measurable_const_mul _)]
  congr 1
  ext y
  simp [mul_assoc]
end GlobalTheory.CompanionTheory.HaarPK
