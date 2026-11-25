-- Prove2me | solution 1 for GroundTheory.Global.inner_mixedToEuclideanConj_mixedToEuclidean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:54.140881+00:00
-- url     : https://prove2.me/submissions/d936faed-d5db-4599-ac81-b306216c1f0b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (β a : mixedSpace K) :
    ⟪mixedToEuclideanConj K β, mixedToEuclidean K a⟫ = mixedTraceForm K β a := by
  rw [real_inner_comm, ← mixedTraceForm_eq_inner, mixedTraceForm_comm]
end GroundTheory.Global
