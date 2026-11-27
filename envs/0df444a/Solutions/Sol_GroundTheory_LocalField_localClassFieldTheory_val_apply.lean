-- Prove2me | solution 1 for GroundTheory.LocalField.localClassFieldTheory_val_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:29.952359+00:00
-- url     : https://prove2.me/submissions/cc40e536-9631-483d-b636-ca677655922c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalAxiom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Abstract ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    ((localClassFieldTheory K Ω).val a).toAdd = ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) :=
  rfl
end GroundTheory.LocalField
