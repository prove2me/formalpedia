-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.finrank_adjoin_genX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:43:07.445853+00:00
-- url     : https://prove2.me/submissions/a3e0fbdc-8270-40e3-b5de-5437fd60c932

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_not_mem
import Theorems.Thm_GroundTheory_Arith_Abelian_adjoin_genX_genY
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


section
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
section Generic
end Generic
section Lift
variable {L : Type*} [Field L] [Algebra F L] {u v : L}
end Lift
section GenericPoint
private theorem genY_sq : genY W ^ 2 + coefB W * genY W - coefC W = 0 := by
  have e := (equation_iff _ _).mp (equation_gen W)
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [coefB, coefC]
  linear_combination e
variable [W.IsElliptic]
end GenericPoint
end GroundTheory.Arith.Abelian
end

set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : Module.finrank (IntermediateField.adjoin F {genX W})
    W.toAffine.FunctionField = 2 := by
  set E1 := IntermediateField.adjoin F {genX W}
  have hx : genX W ∈ E1 := IntermediateField.mem_adjoin_simple_self F _
  have hb : coefB W ∈ E1 := by
    simp only [coefB]
    exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hx)
      (IntermediateField.algebraMap_mem _ _)
  have hc : coefC W ∈ E1 := by
    simp only [coefC]
    exact add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem hx 2)))
      (mul_mem (IntermediateField.algebraMap_mem _ _) hx)) (IntermediateField.algebraMap_mem _ _)
  set q : E1[X] := X ^ 2 + C ⟨coefB W, hb⟩ * X - C ⟨coefC W, hc⟩
  have hq : aeval (genY W) q = 0 := by
    simp only [q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    exact genY_sq W
  have hqdeg : q.natDegree = 2 := by simp only [q]; compute_degree!
  have hq0 : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hqdeg; exact absurd hqdeg (by decide)
  have hint : IsIntegral E1 (genY W) := (show IsAlgebraic E1 (genY W) from ⟨q, hq0, hq⟩).isIntegral
  have hdeg : (minpoly E1 (genY W)).natDegree = 2 := by
    have hle : (minpoly E1 (genY W)).natDegree ≤ 2 := by
      rw [← hqdeg]
      exact natDegree_le_of_dvd (minpoly.dvd E1 _ hq) hq0
    have hne1 : (minpoly E1 (genY W)).natDegree ≠ 1 := by
      intro h1
      rw [minpoly.natDegree_eq_one_iff] at h1
      obtain ⟨z, hz⟩ := h1
      exact genY_not_mem W (hz ▸ z.2)
    have hpos := minpoly.natDegree_pos hint
    omega
  have htop : IntermediateField.adjoin E1 {genY W} = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY W
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, hdeg]
end GroundTheory.Arith.Abelian
