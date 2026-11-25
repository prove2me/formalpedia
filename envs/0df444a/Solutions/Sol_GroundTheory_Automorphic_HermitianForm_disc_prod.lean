-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.disc_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:37:44.869267+00:00
-- url     : https://prove2.me/submissions/dc5200e3-248b-487e-8156-02374d51a2e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_algebraMap_detUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
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
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix GroundTheory.LocalField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
open GroundTheory.Automorphic.HermitianForm
variable [Algebra.IsSeparable F E]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') : (h.prod h').disc = h.disc * h'.disc := by
  set b := Module.finBasis E V
  set b' := Module.finBasis E V'
  rw [(h.prod h').disc_eq (b.prod b'), h.disc_eq b, h'.disc_eq b', ← QuotientGroup.mk_mul]
  congr 1
  apply Units.ext
  apply (algebraMap F E).injective
  rw [Units.val_mul, map_mul, algebraMap_detUnit, algebraMap_detUnit, algebraMap_detUnit]
  have : gram (h.prod h').toSesq (b.prod b') =
      fromBlocks (gram h.toSesq b) 0 0 (gram h'.toSesq b') := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [gram_apply, Basis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        LinearMap.inl_apply, LinearMap.inr_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply] <;>
      rw [prod_apply] <;>
      simp only [LinearMap.map_zero, LinearMap.zero_apply, add_zero, zero_add]
  rw [this, det_fromBlocks_zero₂₁]
end GroundTheory.Automorphic.HermitianForm
