-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.disc_of_finrank_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:06.815964+00:00
-- url     : https://prove2.me/submissions/0128db80-1f63-4744-9b0a-5087c335257d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_algebraMap_detUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix GroundTheory.LocalField
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
open GroundTheory.Automorphic.HermitianForm
variable [Algebra.IsSeparable F E]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [FiniteDimensional E V] (h : HermitianForm F E V)
    (hV : finrank E V = 0) : h.disc = 1 := by
  have : IsEmpty (Fin (finrank E V)) := by rw [hV]; infer_instance
  rw [disc]
  convert QuotientGroup.mk_one (normUnits F E).range
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, det_isEmpty, Units.val_one, map_one]
end GroundTheory.Automorphic.HermitianForm
