-- Prove2me | solution 1 for GroundTheory.LocalField.ordRat_le_ordRat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:36.562954+00:00
-- url     : https://prove2.me/submissions/1df9e62b-7189-489a-92d3-30d0197acae3

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Theorems.Thm_GroundTheory_LocalField_valuation_algebraMap_le_iff
import Theorems.Thm_GroundTheory_LocalField_ord_le_ord_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]
variable {K}
variable [Algebra.IsAlgebraic K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x ≤ ordRat K y ↔ valuation Ω y ≤ valuation Ω x := by
  obtain ⟨m, a, hm, ha, h⟩ := exists_valuation_pow_eq (K := K) hx
  obtain ⟨n, b, hn, hb, h'⟩ := exists_valuation_pow_eq (K := K) hy
  have hmn : m * n ≠ 0 := (Nat.mul_pos hm hn).ne'
  have hp : valuation Ω y ^ (m * n) ≤ valuation Ω x ^ (m * n) ↔
      valuation Ω y ≤ valuation Ω x := pow_le_pow_iff_left₀ zero_le zero_le hmn
  rw [← hp]
  have e1 : valuation Ω x ^ (m * n) = valuation Ω (algebraMap K Ω (a ^ n)) := by
    rw [pow_mul, h, map_pow, map_pow]
  have e2 : valuation Ω y ^ (m * n) = valuation Ω (algebraMap K Ω (b ^ m)) := by
    rw [mul_comm, pow_mul, h', map_pow, map_pow]
  rw [e1, e2, valuation_algebraMap_le_iff, ← ord_le_ord_iff (pow_ne_zero _ ha) (pow_ne_zero _ hb),
    ordRat_eq_of_pow hm ha h, ordRat_eq_of_pow hn hb h', ord_pow_alt, ord_pow_alt]
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ hm' hn']
  constructor
  · intro hle
    have h2 : (((n : ℤ) * ord a : ℤ) : ℚ) ≤ (((m : ℤ) * ord b : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · intro hle
    have : ((n : ℤ) : ℚ) * ord a ≤ ((m : ℤ) : ℚ) * ord b := by exact_mod_cast hle
    push_cast at this
    linarith
end GroundTheory.LocalField
