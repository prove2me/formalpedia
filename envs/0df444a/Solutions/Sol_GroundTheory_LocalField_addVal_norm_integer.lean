-- Prove2me | solution 1 for GroundTheory.LocalField.addVal_norm_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:29.146713+00:00
-- url     : https://prove2.me/submissions/fad04324-38f7-4402-a8be-a76f702c2c5e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_ord_eq_of_addVal_eq
import Theorems.Thm_GroundTheory_LocalField_coe_norm_integer
import Theorems.Thm_GroundTheory_LocalField_exists_addVal_eq_coe
import Theorems.Thm_GroundTheory_LocalField_ord_norm
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos


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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
variable {K L}
variable [Algebra.IsSeparable K L]
namespace GroundTheory.LocalField
theorem _root_.solution (y : 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.norm 𝒪[K] y) =
      residueDegree K L • IsDiscreteValuationRing.addVal 𝒪[L] y := by
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero,
      nsmul_eq_mul]
    have := residueDegree_pos K L
    rw [ENat.mul_top (by exact_mod_cast this.ne')]
  have hN : Algebra.norm 𝒪[K] y ≠ 0 := by
    intro h
    have h2 : Algebra.norm K (y : L) = 0 := by rw [← coe_norm_integer, h]; rfl
    rw [Algebra.norm_eq_zero_iff] at h2
    exact hy (Subtype.ext h2)
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe hN
  obtain ⟨d, hd⟩ := exists_addVal_eq_coe hy
  have h1 := ord_eq_of_addVal_eq hN hk
  have h2 := ord_eq_of_addVal_eq hy hd
  rw [coe_norm_integer, ord_norm, h2] at h1
  rw [hk, hd, nsmul_eq_mul]
  have : k = residueDegree K L * d := by exact_mod_cast h1.symm
  rw [this]
  push_cast
  rfl
end GroundTheory.LocalField
