-- Prove2me | solution 1 for GlobalTheory.lt_add_smul_of_abs_polar_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:37.881915+00:00
-- url     : https://prove2.me/submissions/2d91028e-1909-451e-81f7-175e9d800c8b

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
theorem _root_.solution (q : QuadraticMap ℤ X ℝ) {e μ : X} {c : ℝ} {N : ℤ}
    (hc : 0 ≤ c) (hN : 2 * c < N) (hμ : 0 < q μ)
    (h : |QuadraticMap.polar q e μ| ≤ c * QuadraticMap.polar q μ μ) :
    q e < q (e + N • μ) ∧ q (-e) < q (-e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  rw [QuadraticMap.polar_self, nsmul_eq_mul, abs_le] at h
  have h1 := mul_pos hN0 (mul_pos (sub_pos.2 hN) hμ)
  have h2 := mul_le_mul_of_nonneg_left h.1 hN0.le
  have h3 := mul_le_mul_of_nonneg_left h.2 hN0.le
  simp only [QuadraticMap.map_add q, QuadraticMap.polar_smul_right, QuadraticMap.polar_neg_left,
    QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast at h2 h3 ⊢
  constructor <;> nlinarith
end GlobalTheory
