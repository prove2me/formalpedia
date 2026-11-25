-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.inner_euclidPiEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:09:38.175293+00:00
-- url     : https://prove2.me/submissions/cfaca13c-29b3-429c-88b7-2b6d7c8f131f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite

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
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution (u v : ι → euclidean.mixedSpace K) :
    ⟪euclidPiEquiv K u, euclidPiEquiv K v⟫ = ∑ i, ⟪u i, v i⟫ := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← (stdOrthonormalBasis ℝ (euclidean.mixedSpace K)).repr.inner_map_map (u i) (v i),
    PiLp.inner_apply]
  rfl
end GroundTheory.Automorphic.GJMatrix
