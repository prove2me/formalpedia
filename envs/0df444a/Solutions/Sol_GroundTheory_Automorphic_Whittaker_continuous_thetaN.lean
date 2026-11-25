-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.continuous_thetaN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:28.569126+00:00
-- url     : https://prove2.me/submissions/ba068b5a-40b1-4eba-b895-f5c1536bc6df

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ}
variable [IsTopologicalRing F]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution :
    Continuous (thetaN : Iwasawa.unipotent F n → Iwasawa.unipotent F n) :=
  (continuous_theta.comp continuous_subtype_val).subtype_mk _
end GroundTheory.Automorphic.Whittaker
