-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.disc_ofUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:37:23.719863+00:00
-- url     : https://prove2.me/submissions/a11984c0-a796-49da-94cd-816e70865a69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_algebraMap_detUnit
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_disc_eq

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
theorem _root_.solution (a : Fˣ) : (ofUnit (E := E) a).disc = QuotientGroup.mk a := by
  rw [disc_eq _ (Basis.singleton (Fin 1) E)]
  congr 1
  apply Units.ext
  apply (algebraMap F E).injective
  rw [algebraMap_detUnit, det_unique, gram_apply, Basis.singleton_apply, ofUnit_apply, map_one,
    one_mul, mul_one]
end GroundTheory.Automorphic.HermitianForm
