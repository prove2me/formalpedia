-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.continuous_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:10.435331+00:00
-- url     : https://prove2.me/submissions/876a5d96-27bc-4a0a-9317-cba024384b54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups

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
theorem _root_.solution : Continuous (theta : GL (Fin n) F → GL (Fin n) F) :=
  continuous_sigma.inv
end GroundTheory.Automorphic.Whittaker
