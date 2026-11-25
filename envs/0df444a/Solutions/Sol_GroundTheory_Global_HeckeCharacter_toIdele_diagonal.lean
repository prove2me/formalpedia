-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.toIdele_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:21:48.705906+00:00
-- url     : https://prove2.me/submissions/e4266e4b-3a9f-47bf-b99c-f56538eeccb9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_apply
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution (a : Kˣ) : χ.toIdele (diagonal K a) = 1 := by
  rw [toIdele_apply, IdeleClassGroup.mk_diagonal, map_one]
end GroundTheory.Global.HeckeCharacter
