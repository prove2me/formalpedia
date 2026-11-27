-- Prove2me | solution 1 for GroundTheory.ProfCoh.isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:50.3688+00:00
-- url     : https://prove2.me/submissions/1d1af169-aa29-40ae-853e-cf8c22b5a59e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_isPGroup_primaryQuotientPreimage_quotient

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
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution {l : ℕ}
    (hl : l.Prime) :
    IsPGroup l (primaryQuotientPreimage (lowerRamificationGroup K L 0) l ⧸
      (coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l).subgroupOf
        (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) :=
  isPGroup_primaryQuotientPreimage_quotient _ _ hl
end GroundTheory.ProfCoh
