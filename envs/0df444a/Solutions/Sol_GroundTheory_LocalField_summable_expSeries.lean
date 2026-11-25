-- Prove2me | solution 1 for GroundTheory.LocalField.summable_expSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:25.732833+00:00
-- url     : https://prove2.me/submissions/5d529567-11e4-412c-a5e8-57683993e483

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
import Theorems.Thm_GroundTheory_LocalField_tendsto_zero_iff_valBall
import Theorems.Thm_GroundTheory_LocalField_summable_of_tendsto_zero
import Theorems.Thm_GroundTheory_LocalField_expTerm_mem
import Theorems.Thm_GroundTheory_LocalField_expTerm_order_bound
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
    Summable fun k : ℕ ↦ x ^ k / (k.factorial : K) := by
  refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
  rw [eventually_atTop]
  refine ⟨(p - 1) * N.toNat, fun k hk ↦ valBall_antitone ?_ (expTerm_mem p hx k)⟩
  have h1 := expTerm_order_bound p ha k
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    rw [Nat.cast_sub hp.out.one_le]; simp
  have h3 : (((p - 1) * N.toNat : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  push_cast [hp1] at h3
  nlinarith
end GroundTheory.LocalField
