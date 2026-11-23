-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.abs_norm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:31.042794+00:00
-- url     : https://prove2.me/submissions/0a336025-7f49-4822-bb5d-b468da0e8412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_prod_emb


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
theorem _root_.solution [IsTotallyReal F] (ν : F) :
    ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) = ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ) := by
  have h := prod_emb ν
  have h' : ((Algebra.norm ℚ ν : ℚ) : ℝ) = ∏ τ : Emb F, τ ν := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_prod, h]; push_cast; rfl
  rw [h', Finset.abs_prod, Complex.ofReal_prod]
end GlobalTheory.HeckeTwoExp
