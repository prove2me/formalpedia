-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedPairingPi_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:31.913449+00:00
-- url     : https://prove2.me/submissions/58acfcf3-0c0f-419a-a14d-a1a06528d4c0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_inner_euclidPiEquiv
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner


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
theorem _root_.solution (x y : ι → mixedSpace K) :
    mixedPairingPi K x y = ⟪toEuclidPi K x, toEuclidPiConj K y⟫ := by
  rw [toEuclidPi, toEuclidPiConj, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply, inner_euclidPiEquiv, mixedPairingPi]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mixedTraceForm_eq_inner]
  rfl
end GroundTheory.Automorphic.GJMatrix
