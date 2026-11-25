-- Prove2me | solution 1 for GroundTheory.LocalField.span_singleton_eq_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:29.16478+00:00
-- url     : https://prove2.me/submissions/37e1133b-aa2e-4e55-871b-32462046ee2e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different

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
open ValuativeRel Polynomial
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance high] FaithfulSMul.to_isTorsionFree
open IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GroundTheory.LocalField
theorem _root_.solution {a : R} (ha : a ≠ 0) {n : ℕ} (hn : addVal R a = n) :
    Ideal.span {a} = IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hm : m = n := by
    rw [addVal_mul, addVal_pow, addVal_uniformizer hϖ, addVal_eq_zero_of_unit, zero_add,
      nsmul_eq_mul, mul_one] at hn
    exact_mod_cast hn
  rw [← hm, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    hϖ.maximalIdeal_eq]
end GroundTheory.LocalField
