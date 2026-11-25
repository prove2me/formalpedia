-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.localComponent_eq_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:36.385405+00:00
-- url     : https://prove2.me/submissions/ebb4b863-ca34-4e7f-a6a3-f15d74d0cb58

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_not_dvd_conductor_iff
import Theorems.Thm_GroundTheory_Global_IdeleGroup_not_dvd_conductor_iff


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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {a : (v.adicCompletion K)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    χ.localComponent v a = 1 :=
  (χ.not_dvd_conductor_iff v).1 hv ha
end GroundTheory.Global.HeckeCharacter
