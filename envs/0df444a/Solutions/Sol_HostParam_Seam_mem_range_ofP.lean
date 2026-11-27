-- Prove2me | solution 1 for HostParam.Seam.mem_range_ofP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:31.3598+00:00
-- url     : https://prove2.me/submissions/5a6a0ee9-e89e-402d-9958-6a89b26b36bf

import Definitions.Def_Development_AutomorphicArithmetic_QuadraticCharacters_MemRealCyclotomicSubgroup
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_OfPInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC Formalism.FrobeniusOrbits
noncomputable section
open HostParam HostParam.Seam
namespace HostParam.Seam
theorem _root_.solution (κ : PrimChar) : κ ∈ Set.range ofP ↔ 0 < κ.1 ∧ κ.2.IsPrimitive :=
  ⟨by rintro ⟨ψ, rfl⟩; exact ⟨ofP_fst_pos ψ, ofP_snd_isPrimitive ψ⟩, fun h => ⟨toP κ h.1 h.2, rfl⟩⟩
end HostParam.Seam
