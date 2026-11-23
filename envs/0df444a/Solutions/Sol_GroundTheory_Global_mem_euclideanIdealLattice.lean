-- Prove2me | solution 1 for GroundTheory.Global.mem_euclideanIdealLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:29.282197+00:00
-- url     : https://prove2.me/submissions/bd86ba6f-adb0-4960-91dd-2e242e8cdaa5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean

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
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (u : euclidean.mixedSpace K) :
    u ∈ euclideanIdealLattice K I ↔ (mixedToEuclidean K).symm u ∈ idealLattice K I := Iff.rfl
end GroundTheory.Global
