-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.covolume_idealLattice2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:24.707818+00:00
-- url     : https://prove2.me/submissions/bd4bc908-096b-442c-b1c4-0e8e0c9c6df2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_isAddFundamentalDomain_idealLattice2
import Theorems.Thm_GroundTheory_Global_covolume_idealLattice_selfDualMeasure


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
    ZLattice.covolume (idealLattice2 I) (mixedMeasure2 K) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_idealLattice2 I),
    measureReal_def, mixedMeasure2, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← covolume_idealLattice_selfDualMeasure, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (idealLattice K (I i))) _),
    measureReal_def]
end GroundTheory.Automorphic.Adele2
