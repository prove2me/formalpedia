-- Prove2me | solution 1 for GroundTheory.LocalField.normalizedValuation_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:29.135858+00:00
-- url     : https://prove2.me/submissions/ee4898e4-888d-446f-a29a-50447693b561

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_natCast_prime
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_natCast_of_not_dvd
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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    normalizedValuation K (n : K) =
      WithZero.exp (-(absRamificationIndex K * padicValNat p n : ℤ)) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm]
  push_cast
  rw [map_mul, map_pow, normalizedValuation_natCast_prime p,
    normalizedValuation_natCast_of_not_dvd p hm, mul_one, ← WithZero.exp_nsmul]
  congr 1
  simp; ring
end GroundTheory.LocalField
