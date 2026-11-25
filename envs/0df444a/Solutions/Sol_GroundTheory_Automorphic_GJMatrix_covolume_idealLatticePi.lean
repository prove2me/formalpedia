-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.covolume_idealLatticePi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:24.338797+00:00
-- url     : https://prove2.me/submissions/39d5980d-2984-438f-b2c0-92d37266dd50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_isAddFundamentalDomain_idealLatticePi
import Theorems.Thm_GroundTheory_Global_covolume_idealLattice_selfDualMeasure


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
    ZLattice.covolume (idealLatticePi I) (mixedMeasurePi K) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain_idealLatticePi I),
    measureReal_def, mixedMeasurePi, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← covolume_idealLattice_selfDualMeasure, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (idealLattice K (I i))) _),
    measureReal_def]
end GroundTheory.Automorphic.GJMatrix
