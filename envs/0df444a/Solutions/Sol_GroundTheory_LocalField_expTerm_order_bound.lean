-- Prove2me | solution 1 for GroundTheory.LocalField.expTerm_order_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:28.209774+00:00
-- url     : https://prove2.me/submissions/0c2324b4-9210-46eb-9c6f-a622cf2f9df2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_sub_one_mul_padicValNat_factorial_le
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
omit [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a)
    (k : ℕ) : (k : ℤ) ≤ (p - 1 : ℤ) * (k * a - absRamificationIndex K * padicValNat p k.factorial)
    := by
  have h1 := sub_one_mul_padicValNat_factorial_le p k
  set v := padicValNat p k.factorial
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  have h1' : ((p : ℤ) - 1) * v ≤ k := by
    have hp1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
      rw [Nat.cast_sub hp.out.one_le]; simp
    have : (((p - 1) * v : ℕ) : ℤ) ≤ k := by exact_mod_cast h1
    push_cast [hp1] at this
    linarith
  have he : (0 : ℤ) ≤ e := by positivity
  have hk : (0 : ℤ) ≤ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1' he, mul_le_mul_of_nonneg_left ha.le hk]
end GroundTheory.LocalField
