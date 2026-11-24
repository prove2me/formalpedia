-- Prove2me | solution 1 for GlobalTheory.SphereMeanDrop.eval_blockScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:39.544898+00:00
-- url     : https://prove2.me/submissions/3fce236f-281c-4311-bb5c-0a0649883463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMultiHomogeneousRenameCastLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights
namespace GlobalTheory.SphereMeanDrop
theorem _root_.solution {B n : ℕ} (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hm : IsMultiHomogeneous a g) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    eval (fun p => r p.1 * x p) g = (∏ b, r b ^ a b) * eval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [eval_monomial, eval_monomial]
  have h1 : (s.prod fun p e => (r p.1 * x p) ^ e) =
      (s.prod fun p e => r p.1 ^ e) * s.prod fun p e => x p ^ e := by
    rw [← Finsupp.prod_mul]
    congr 1
    funext p e
    rw [mul_pow]
  have h2 : (s.prod fun p e => r p.1 ^ e) = ∏ b, r b ^ a b := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ y, r b ^ s (b, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hm s hs b]
  rw [h1, h2]
  ring
end GlobalTheory.SphereMeanDrop
