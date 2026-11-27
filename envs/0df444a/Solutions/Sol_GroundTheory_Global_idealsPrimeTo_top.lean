-- Prove2me | solution 1 for GroundTheory.Global.idealsPrimeTo_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:47.142907+00:00
-- url     : https://prove2.me/submissions/6862fa1e-6d32-4b1e-b60d-29cac30451c2

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
namespace GroundTheory.Global
theorem _root_.solution : idealsPrimeTo (⊤ : Ideal (𝓞 K)) = ⊤ := by
  exact eq_top_iff.2 fun I _ v hv ↦
    absurd (top_le_iff.1 (Ideal.le_of_dvd hv)) v.isPrime.ne_top
end GroundTheory.Global
