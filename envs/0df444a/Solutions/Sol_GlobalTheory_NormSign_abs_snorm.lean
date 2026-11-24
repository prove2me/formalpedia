-- Prove2me | solution 1 for GlobalTheory.NormSign.abs_snorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:29.127475+00:00
-- url     : https://prove2.me/submissions/92514754-a69f-4c43-ba23-213fb83c0cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.NormSign
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.NormSign
theorem _root_.solution (x : mixedSpace K) : |snorm x| = mixedEmbedding.norm x := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, snorm, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (by positivity)]
end GlobalTheory.NormSign
