-- Prove2me | solution 1 for GlobalTheory.LowestWeight.finite_lminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:16.125202+00:00
-- url     : https://prove2.me/submissions/47884a35-29b9-4973-93ab-c7c2c9aa5bff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LowestWeightFunctionMulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix Filter Topology
open scoped ComplexConjugate ComplexOrder
open GlobalTheory.LowestWeight
variable {r : ℕ}
namespace GlobalTheory.LowestWeight
theorem _root_.solution (Y : Matrix (Fin r) (Fin r) ℂ) (i : Fin (r + 1)) :
    {s : ℂ | lminor (Y + s • (1 : Matrix (Fin r) (Fin r) ℂ)) i = 0}.Finite := by
  have hi := Nat.le_of_lt_succ i.isLt
  refine (Polynomial.finite_setOf_isRoot
    (Matrix.charpoly_monic (-(Y.submatrix (Fin.castLE hi) (Fin.castLE hi)))).ne_zero).subset ?_
  intro s hs
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly] at hs ⊢
  rw [← hs, lminor]
  congr 1
  ext a b
  simp only [submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply,
    scalar_apply, Matrix.diagonal_apply, Matrix.neg_apply, sub_neg_eq_add, smul_eq_mul, mul_ite,
    mul_one, mul_zero, (Fin.castLE_injective hi).eq_iff]
  exact add_comm _ _
end GlobalTheory.LowestWeight
