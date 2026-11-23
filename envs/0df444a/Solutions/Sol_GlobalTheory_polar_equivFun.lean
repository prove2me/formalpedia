-- Prove2me | solution 1 for GlobalTheory.polar_equivFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:05.823859+00:00
-- url     : https://prove2.me/submissions/35090a41-ccaa-4d7c-b44b-7512c475cc06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul



set_option autoImplicit false
noncomputable section
open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder
open GlobalTheory
open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
variable {X : Type*} [AddCommGroup X] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x y : X) :
    ReciprocityTheory.ReducedBases.polar (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j))
      (b.equivFun x) (b.equivFun y) = QuadraticMap.polar q x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y, ← QuadraticMap.polarBilin_apply_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, of_apply,
    mul_sum, Basis.equivFun_apply, zsmul_eq_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
end GlobalTheory
