-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.covolume_euclidLattice2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:38.566037+00:00
-- url     : https://prove2.me/submissions/1b7e185c-af6e-43bd-92b0-edcc6007a99e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_measurePreserving_toEuclid2_symm
import Theorems.Thm_GroundTheory_Automorphic_Adele2_covolume_idealLattice2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution (I : Fin 2 → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (euclidLattice2 I) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_comap (idealLattice2 I) (mixedMeasure2 K) volume
    (measurePreserving_toEuclid2_symm K), covolume_idealLattice2]
end GroundTheory.Automorphic.Adele2
