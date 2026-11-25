-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.covolume_euclidLatticePi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:39.035384+00:00
-- url     : https://prove2.me/submissions/7e01d4e3-9979-4185-bb80-5978226e6459

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_toEuclidPi_symm
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_covolume_idealLatticePi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclidLatticePi I) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_comap (idealLatticePi I) (mixedMeasurePi K) volume
    (measurePreserving_toEuclidPi_symm K), covolume_idealLatticePi]
end GroundTheory.Automorphic.GJMatrix
