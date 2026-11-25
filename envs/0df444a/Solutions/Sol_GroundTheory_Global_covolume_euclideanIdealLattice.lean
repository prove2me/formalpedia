-- Prove2me | solution 1 for GroundTheory.Global.covolume_euclideanIdealLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:01.262098+00:00
-- url     : https://prove2.me/submissions/36a8a26a-cc5d-4e09-8525-0bcf4a219ea0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceDualLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclidean_symm
import Theorems.Thm_GroundTheory_Global_covolume_idealLattice_selfDualMeasure


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
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclideanIdealLattice K I) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  rw [ZLattice.covolume_comap (idealLattice K I) (selfDualMeasure K) volume
    (measurePreserving_mixedToEuclidean_symm K), covolume_idealLattice_selfDualMeasure]
end GroundTheory.Global
