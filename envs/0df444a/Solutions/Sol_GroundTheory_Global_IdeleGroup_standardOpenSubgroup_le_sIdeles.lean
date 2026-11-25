-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.standardOpenSubgroup_le_sIdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:37.318999+00:00
-- url     : https://prove2.me/submissions/a1da7972-0a4d-41a6-8fed-937c2e4e29f4

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
theorem _root_.solution : standardOpenSubgroup K ≤ sIdeles S :=
  fun _ hx v _ ↦ mem_standardOpenSubgroup_iff_ord.1 hx v
end GroundTheory.Global.IdeleGroup
