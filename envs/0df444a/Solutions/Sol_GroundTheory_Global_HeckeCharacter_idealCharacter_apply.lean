-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.idealCharacter_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:35.477492+00:00
-- url     : https://prove2.me/submissions/c6d36160-4231-4c59-b478-3ebacaf509da

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar

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
theorem _root_.solution {x : IdeleGroup K} (hx : x ∈ primeToLevel χ.conductor)
    (I : idealsPrimeTo χ.conductor) (h : toFractionalIdeal x = I) :
    χ.idealCharacter I = χ.toIdele x := by
  obtain ⟨hy, hyI⟩ := (exists_mem_primeToLevel I.2).choose_spec
  exact χ.toIdele_eq_of_toFractionalIdeal_eq hy hx (hyI.trans h.symm)
end GroundTheory.Global.HeckeCharacter
