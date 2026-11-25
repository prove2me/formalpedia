-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.sIdeles_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:08.249747+00:00
-- url     : https://prove2.me/submissions/57ab1d99-39b7-4ac5-a04b-2f02f7208b2d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups

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
theorem _root_.solution {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sIdeles S ≤ sIdeles T :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (h hvS)
end GroundTheory.Global.IdeleGroup
