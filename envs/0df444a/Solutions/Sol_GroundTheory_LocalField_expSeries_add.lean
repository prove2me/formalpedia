-- Prove2me | solution 1 for GroundTheory.LocalField.expSeries_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:01.475965+00:00
-- url     : https://prove2.me/submissions/5386f26f-1c26-4fde-83e9-6ffa25bcbef3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_summable_expSeries
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {a : ℤ} {x y : K} (hx : x ∈ valBall K a) (hy : y ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries (x + y) = expSeries x * expSeries y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  have hsx := summable_expSeries p hx ha
  have hsy := summable_expSeries p hy ha
  have hxy := hsx.mul_of_nonarchimedean hsy
  unfold expSeries
  rw [hsx.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsy hxy]
  refine tsum_congr fun n ↦ ?_
  rw [(Commute.all x y).add_pow', Finset.sum_div]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  obtain ⟨i, j⟩ := ij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  subst hij
  have key : ((i + j).choose i : K) * (i.factorial : K) * (j.factorial : K) =
      ((i + j).factorial : K) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hc : ((i + j).choose i : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right i j)).ne'
  simp only [nsmul_eq_mul]
  rw [← key]
  field_simp
end GroundTheory.LocalField
