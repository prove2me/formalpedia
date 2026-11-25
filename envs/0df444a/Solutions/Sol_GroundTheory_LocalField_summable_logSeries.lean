-- Prove2me | solution 1 for GroundTheory.LocalField.summable_logSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:15.2+00:00
-- url     : https://prove2.me/submissions/b4b87699-e7e2-43f4-9db5-07f13fabbdb3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
import Theorems.Thm_GroundTheory_LocalField_tendsto_zero_iff_valBall
import Theorems.Thm_GroundTheory_LocalField_summable_of_tendsto_zero
import Theorems.Thm_GroundTheory_LocalField_four_mul_padicValNat_le
import Theorems.Thm_GroundTheory_LocalField_logTerm_mem
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
include p
namespace GroundTheory.LocalField
theorem _root_.solution {x : K} (hx : x ∈ valBall K 1) :
    Summable fun k : ℕ ↦ (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) := by
  refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
  rw [eventually_atTop]
  set e := absRamificationIndex K
  refine ⟨4 * N.toNat + 32 * e ^ 2, fun k hk ↦ valBall_antitone ?_ (logTerm_mem p hx k)⟩
  have h1 := four_mul_padicValNat_le p e (Nat.succ_ne_zero k)
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : ((4 * N.toNat + 32 * e ^ 2 : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  have h4 : ((4 * e * padicValNat p (k + 1) : ℕ) : ℤ) ≤ ((k + 1 + 32 * e ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    ] at h3 h4
  nlinarith
end GroundTheory.LocalField
