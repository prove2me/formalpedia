-- Prove2me | solution 1 for GroundTheory.LocalField.discr_powerBasis_eq_norm_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:57:04.981976+00:00
-- url     : https://prove2.me/submissions/002ba822-3ec8-4105-981c-ad6cd41df724

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_norm_integer
import Theorems.Thm_GroundTheory_LocalField_isLocalization_integer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
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
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



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
theorem _root_.solution {x : 𝒪[L]} (hint : IsIntegral 𝒪[K] x)
    (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    ∃ s : ℕ, Algebra.discr 𝒪[K] (PowerBasis.ofAdjoinEqTop' hint hx).basis =
      (-1) ^ s * Algebra.norm 𝒪[K] (aeval x (derivative (minpoly 𝒪[K] x))) := by
  classical
  set pb := PowerBasis.ofAdjoinEqTop' hint hx
  have := isLocalization_integer K L
  let bK : Module.Basis (Fin pb.dim) K L :=
    pb.basis.localizationLocalization K (nonZeroDivisors 𝒪[K]) L
  let pb' : PowerBasis K L :=
    { gen := algebraMap 𝒪[L] L x
      dim := pb.dim
      basis := bK
      basis_eq_pow := fun i ↦ by
        simp only [bK, Module.Basis.localizationLocalization_apply, PowerBasis.coe_basis, map_pow,
          pb, PowerBasis.ofAdjoinEqTop'_gen] }
  have hd := Algebra.discr_localizationLocalization 𝒪[K] (Rₘ := K) (nonZeroDivisors 𝒪[K]) L pb.basis
  have hn := Algebra.discr_powerBasis_eq_norm (K := K) (L := L) pb'
  refine ⟨Module.finrank K L * (Module.finrank K L - 1) / 2, ?_⟩
  apply Subtype.ext
  change algebraMap 𝒪[K] K _ = _
  rw [← hd]
  change Algebra.discr K pb'.basis = _
  rw [hn, Subring.coe_mul, Subring.coe_pow, coe_norm_integer]
  congr 2
  have hm := minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  simp only [pb']
  rw [hm, derivative_map, aeval_map_algebraMap, aeval_algebraMap_apply]
  rfl
end GroundTheory.LocalField
