-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.LatSum.prod_abs_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:57.368682+00:00
-- url     : https://prove2.me/submissions/66ac2075-7c71-40fc-a63b-26cba4898a02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]
namespace GlobalTheory.HeckeTwo.LatSum
theorem _root_.solution (x : F) : ∏ τ : Emb F, |τ x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := congrArg (fun z : ℂ => ‖z‖) (prod_emb x)
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs] at h
  rw [h, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
end GlobalTheory.HeckeTwo.LatSum
