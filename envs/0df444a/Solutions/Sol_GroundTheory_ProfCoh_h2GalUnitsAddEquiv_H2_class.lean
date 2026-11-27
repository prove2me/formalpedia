-- Prove2me | solution 1 for GroundTheory.ProfCoh.h2GalUnitsAddEquiv_H2_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:57.521842+00:00
-- url     : https://prove2.me/submissions/d392e31e-aef8-4297-940e-803f4a5c686d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars
import Theorems.Thm_GroundTheory_ProfCoh_h2IntRepAddEquiv_H2_class

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
variable (K L : Type) [Field K] [Field L] [Algebra K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (x : cocycles₂ (galUnits K L)) :
    h2GalUnitsAddEquiv K L ((H2π _).hom x) =
      (H2π _).hom (cocycles₂IntRepAddEquiv (galUnitsHom K L) x) :=
  h2IntRepAddEquiv_H2_class (galUnitsHom K L) x
end GroundTheory.ProfCoh
