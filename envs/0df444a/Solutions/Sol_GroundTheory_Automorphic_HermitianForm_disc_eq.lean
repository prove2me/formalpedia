-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.disc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:46:16.151304+00:00
-- url     : https://prove2.me/submissions/f8dbc480-5d09-4100-b07c-4d05ac3112fe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_detUnit_eq_of_det_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_detUnit_basis_change
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
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι E V) : h.disc = QuotientGroup.mk (h.detUnit b) := by
  have hcard : Fintype.card ι = Fintype.card (Fin (finrank E V)) := by
    rw [Fintype.card_fin, Module.finrank_eq_card_basis b]
  set e : ι ≃ Fin (finrank E V) := Fintype.equivOfCardEq hcard
  have h1 : h.detUnit (b.reindex e) = h.detUnit b := by
    apply detUnit_eq_of_det_eq
    have : gram h.toSesq (b.reindex e) = (gram h.toSesq b).submatrix e.symm e.symm := by
      ext i j; simp [gram_apply, Basis.reindex_apply]
    rw [this, det_submatrix_equiv_self]
  obtain ⟨u, hu⟩ := h.detUnit_basis_change (Module.finBasis E V) (b.reindex e)
  rw [disc, ← h1, hu]
  exact QuotientGroup.eq.2 (MonoidHom.mem_range.2 ⟨u, by rw [inv_mul_cancel_left]⟩)
end GroundTheory.Automorphic.HermitianForm
