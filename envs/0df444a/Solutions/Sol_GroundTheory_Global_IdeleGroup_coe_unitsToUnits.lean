-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_unitsToUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:12.224676+00:00
-- url     : https://prove2.me/submissions/1428e5a1-41be-40d9-9d51-7db94751d766

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound

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
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
omit [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (u : (𝓞 K)ˣ) : ((unitsToUnits K u : Kˣ) : K) = ((u : 𝓞 K) : K) :=
  rfl
end GroundTheory.Global.IdeleGroup
