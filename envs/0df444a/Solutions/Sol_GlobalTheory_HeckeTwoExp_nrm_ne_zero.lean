-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.nrm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:33.675275+00:00
-- url     : https://prove2.me/submissions/af4ce095-00d4-4d01-8e72-f2a00a30f5e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd

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
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution (𝔞 : Frac F) : nrm 𝔞 ≠ 0 := by
  unfold nrm
  rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
  exact 𝔞.ne_zero
end GlobalTheory.HeckeTwoExp
