-- Prove2me | solution 1 for GroundTheory.LocalField.addVal_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:07.829886+00:00
-- url     : https://prove2.me/submissions/79387b08-a6cc-4492-a322-9762a2a56601

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_differentExponent_eq_addVal
import Theorems.Thm_GroundTheory_LocalField_associated_discr
import Theorems.Thm_GroundTheory_LocalField_addVal_norm_integer
import Theorems.Thm_GroundTheory_LocalField_discr_powerBasis_eq_norm_integer
import Theorems.Thm_GroundTheory_LocalField_exists_integer_adjoin_eq_top


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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) =
      (residueDegree K L * differentExponent K L : ℕ) := by
  obtain ⟨x, hx⟩ := exists_integer_adjoin_eq_top K L
  have hint : IsIntegral 𝒪[K] x := Algebra.IsIntegral.isIntegral x
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr
    (associated_discr (PowerBasis.ofAdjoinEqTop' hint hx).basis b)]
  obtain ⟨s, hs⟩ := discr_powerBasis_eq_norm_integer hint hx
  rw [hs, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
    ((isUnit_neg_one).pow s), zero_add, addVal_norm_integer, ← differentExponent_eq_addVal hx]
  push_cast
  rw [nsmul_eq_mul]
end GroundTheory.LocalField
