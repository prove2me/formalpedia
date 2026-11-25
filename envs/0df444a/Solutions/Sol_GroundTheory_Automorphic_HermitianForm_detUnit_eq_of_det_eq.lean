-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.detUnit_eq_of_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:50.629723+00:00
-- url     : https://prove2.me/submissions/58a76f78-4982-44ef-9b32-ac88626e45b6

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
theorem _root_.solution (h : HermitianForm F E V) (h' : HermitianForm F E V')
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι E V) (b' : Basis ι' E V')
    (hb : (gram h.toSesq b).det = (gram h'.toSesq b').det) : h.detUnit b = h'.detUnit b' := by
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, algebraMap_detUnit, hb]
end GroundTheory.Automorphic.HermitianForm
