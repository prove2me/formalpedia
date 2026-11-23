-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.LatSum.norm_mixedEmbedding_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:29.758202+00:00
-- url     : https://prove2.me/submissions/43dc1528-2aa8-40e3-a99d-75f9fb1b0d80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
import Theorems.Thm_GlobalTheory_HeckeTwo_LatSum_abs_le_absSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]
open scoped Classical
namespace GlobalTheory.HeckeTwo.LatSum
theorem _root_.solution (x : F) : ‖mixedEmbedding F x‖ ≤ absSum x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) x,
    Real.norm_eq_abs]
  exact abs_le_absSum x _
end GlobalTheory.HeckeTwo.LatSum
