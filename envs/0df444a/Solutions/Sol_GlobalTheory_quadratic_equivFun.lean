-- Prove2me | solution 1 for GlobalTheory.quadratic_equivFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:36.111479+00:00
-- url     : https://prove2.me/submissions/b644add3-ba0b-4ddb-b859-7d44f1288822

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Theorems.Thm_GlobalTheory_polar_equivFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder
open GlobalTheory
open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
variable {X : Type*} [AddCommGroup X] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x : X) :
    Q (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j)) (b.equivFun x) = q x := by
  rw [Q, polar_equivFun, QuadraticMap.polar_self, nsmul_eq_mul]; push_cast; ring
end GlobalTheory
