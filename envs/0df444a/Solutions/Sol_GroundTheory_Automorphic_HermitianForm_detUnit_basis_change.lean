-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.detUnit_basis_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:34.431029+00:00
-- url     : https://prove2.me/submissions/74e7d646-5c3a-4fd2-b6fa-e1cf5dcae00e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Theorems.Thm_GroundTheory_Automorphic_gram_basis_change
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_algebraMap_detUnit
import Theorems.Thm_GroundTheory_Automorphic_mul_conj
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix GroundTheory.LocalField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
open GroundTheory.Automorphic.HermitianForm
variable [Algebra.IsSeparable F E]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι E V) :
    ∃ u : Eˣ, h.detUnit c = h.detUnit b * normUnits F E u := by
  have hM : IsUnit (b.toMatrix c).det := by
    exact IsUnit.of_mul_eq_one (c.toMatrix b).det
      (by rw [← det_mul, Basis.toMatrix_mul_toMatrix_flip, det_one])
  refine ⟨hM.unit, Units.ext ((algebraMap F E).injective ?_)⟩
  rw [Units.val_mul, map_mul, algebraMap_detUnit, algebraMap_detUnit, coe_normUnits,
    IsUnit.unit_spec, ← mul_conj, gram_basis_change h.toSesq b c, det_mul, det_mul,
    det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, conjHom_apply]
  ring
end GroundTheory.Automorphic.HermitianForm
