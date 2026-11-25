-- Prove2me | solution 1 for GroundTheory.LocalField.natCast_ramificationIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:50:20.857338+00:00
-- url     : https://prove2.me/submissions/a6dfaf24-aa3a-4a51-9ebb-ad430e5190d7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_RamificationTame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped IntermediateField
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    (ramificationIndex K L : 𝓀[L]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro hdvd
  have h1 := Nat.Coprime.eq_one_of_dvd he.symm hdvd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))
end GroundTheory.LocalField
