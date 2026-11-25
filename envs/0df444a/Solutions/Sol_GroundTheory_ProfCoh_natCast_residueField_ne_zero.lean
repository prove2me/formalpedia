-- Prove2me | solution 1 for GroundTheory.ProfCoh.natCast_residueField_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:52.57494+00:00
-- url     : https://prove2.me/submissions/81e28362-841e-4a95-a21d-4574e572842f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure

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
theorem _root_.solution {l : ℕ} (hl : l.Prime) (hlp : l ≠ ringChar 𝓀[K]) :
    (l : 𝓀[L]) ≠ 0 := by
  rw [Ne, ringChar.spec, ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro h
  exact hlp ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hl).1 h).symm
end GroundTheory.ProfCoh
