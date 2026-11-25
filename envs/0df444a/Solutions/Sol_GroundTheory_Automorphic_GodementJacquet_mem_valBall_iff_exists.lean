-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.mem_valBall_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:47.392598+00:00
-- url     : https://prove2.me/submissions/93a13f7b-997a-46e7-92e5-c6c3094dfbdd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_pow
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {r : ℕ} {y : F} :
    y ∈ LocalField.valBall F r ↔ ∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r * a := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hord : LocalField.ord (uniformizer F : F) = 1 :=
    LocalField.ord_uniformizer (irreducible_uniformizer F)
  have hϖr : (uniformizer F : F) ^ r ∈ LocalField.valBall F r := by
    rw [LocalField.mem_valBall_iff_le_ord (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
    simp
  constructor
  · intro hy
    by_cases h0 : y = 0
    · exact ⟨0, zero_mem _, by rw [h0, mul_zero]⟩
    refine ⟨y / (uniformizer F : F) ^ r, ?_, by field_simp⟩
    have hne : y / (uniformizer F : F) ^ r ≠ 0 := div_ne_zero h0 (pow_ne_zero _ hϖ)
    rw [← LocalField.mem_valBall_zero_iff, LocalField.mem_valBall_iff_le_ord hne, div_eq_mul_inv,
      LocalField.ord_mul h0 (inv_ne_zero (pow_ne_zero _ hϖ)),
      LocalField.ord_inv (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
    have := (LocalField.mem_valBall_iff_le_ord h0).1 hy
    linarith
  · rintro ⟨a, ha, rfl⟩
    have := LocalField.mul_mem_valBall hϖr (LocalField.mem_valBall_zero_iff.2 ha)
    simpa using this
end GroundTheory.Automorphic.GodementJacquet
