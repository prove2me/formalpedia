-- Prove2me | solution 1 for GroundTheory.LocalField.expSeries_sub_one_sub_self_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:02.341487+00:00
-- url     : https://prove2.me/submissions/2b2fecd8-9d5f-46c4-b3ec-bde2f52f60ac

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
import Theorems.Thm_GroundTheory_LocalField_tsum_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_expTerm_mem
import Theorems.Thm_GroundTheory_LocalField_expTerm_order_bound
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
theorem _root_.solution {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 - x ∈ valBall K (a + 1) := by
  have hs := summable_expSeries p hx ha
  rw [expSeries, hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one,
    Nat.factorial_one]
  have : ∀ t : K, 1 + (x + t) - 1 - x = t := fun t ↦ by ring
  rw [this]
  refine tsum_mem_valBall fun k ↦ valBall_antitone ?_ (expTerm_mem p hx (k + 1 + 1))
  have h1 := expTerm_order_bound p ha (k + 1 + 1)
  have h0 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega : k + 1 + 1 ≠ 0)
  set v := padicValNat p (k + 1 + 1).factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h0' : (((p - 1) * v : ℕ) : ℤ) < k + 1 + 1 := by exact_mod_cast h0
  push_cast [hp1] at h0' h1
  have he : (0 : ℤ) ≤ e := by positivity
  have h0'' : ((p : ℤ) - 1) * v ≤ k + 1 := by linarith
  have ha' : (e : ℤ) + 1 ≤ ((p : ℤ) - 1) * a := by linarith
  have hk : (0 : ℤ) ≤ k + 1 := by positivity
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h0'' he, mul_le_mul_of_nonneg_left ha' hk]
end GroundTheory.LocalField
