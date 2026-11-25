-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.relfinrank_powField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:19.576396+00:00
-- url     : https://prove2.me/submissions/74ad8e70-eda2-4fcd-bc4d-310eaf441bb4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_pow_not_mem
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



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution : relfinrank F⟮genX E ^ p⟯ (powField E p) = 2 := by
  set K0 := F⟮genX E ^ p⟯
  set w := genY E ^ p
  have hx0 : genX E ^ p ∈ K0 := mem_adjoin_simple_self F _
  have hle : K0 ≤ powField E p := adjoin_simple_le_iff.mpr (subset_adjoin F _ (by simp))
  have hext : K0⟮w⟯ = extendScalars hle := by
    apply restrictScalars_injective F
    rw [adjoin_simple_adjoin_simple, extendScalars_restrictScalars]
    rfl
  have hcst : ∀ a : F, algebraMap F E.toAffine.FunctionField a ∈ K0 := fun a => IntermediateField.algebraMap_mem _ a
  have hb : algebraMap F _ (E.a₁ ^ p) * genX E ^ p + algebraMap F _ (E.a₃ ^ p) ∈ K0 :=
    add_mem (mul_mem (hcst _) hx0) (hcst _)
  have hc : (genX E ^ p) ^ 3 + algebraMap F _ (E.a₂ ^ p) * (genX E ^ p) ^ 2 +
      algebraMap F _ (E.a₄ ^ p) * genX E ^ p + algebraMap F _ (E.a₆ ^ p) ∈ K0 :=
    add_mem (add_mem (add_mem (pow_mem hx0 3) (mul_mem (hcst _) (pow_mem hx0 2)))
      (mul_mem (hcst _) hx0)) (hcst _)
  set q : K0[X] := X ^ 2 + C ⟨_, hb⟩ * X - C ⟨_, hc⟩
  have hq : aeval w q = 0 := by
    have e := (equation_iff _ _).mp (equation_gen E)
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    have e' := congrArg (frobenius E.toAffine.FunctionField p) e
    simp only [map_add, map_mul, map_pow, frobenius_def] at e'
    simp only [q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, w,
      IntermediateField.algebraMap_apply]
    linear_combination e'
  have hqdeg : q.natDegree = 2 := by simp only [q]; compute_degree!
  have hq0 : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hqdeg; exact absurd hqdeg (by decide)
  have hint : IsIntegral K0 w := (show IsAlgebraic K0 w from ⟨q, hq0, hq⟩).isIntegral
  have hdeg : (minpoly K0 w).natDegree = 2 := by
    have hle2 : (minpoly K0 w).natDegree ≤ 2 := by
      rw [← hqdeg]; exact natDegree_le_of_dvd (minpoly.dvd K0 _ hq) hq0
    have hne1 : (minpoly K0 w).natDegree ≠ 1 := by
      intro h1
      rw [minpoly.natDegree_eq_one_iff] at h1
      obtain ⟨z, hz⟩ := h1
      have hw : w ∈ K0 := by rw [← hz]; exact z.2
      exact genY_pow_not_mem E p hw
    have hpos := minpoly.natDegree_pos hint
    omega
  rw [relfinrank_eq_finrank_of_le hle, ← hext, adjoin.finrank hint, hdeg]
end GroundTheory.Arith.Abelian
