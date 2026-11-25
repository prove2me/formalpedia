-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.sUnitsToSIdeles_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:28:10.795868+00:00
-- url     : https://prove2.me/submissions/e688cbaf-8f7c-427f-b489-a650aa34aa89

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Theorems.Thm_GroundTheory_Global_IdeleGroup_diagonal_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : Function.Injective (sUnitsToSIdeles S) := fun _ _ h ↦
  Subtype.ext (diagonal_injective K (congrArg Subtype.val h))
end GroundTheory.Global.IdeleGroup
