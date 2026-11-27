-- Prove2me | solution 1 for HostParam.Seam.ofP_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:34.635584+00:00
-- url     : https://prove2.me/submissions/04fe3e1e-59e9-4151-940e-5b04af6c67c3

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
theorem _root_.solution : Function.Injective ofP := by
  rintro ⟨N, χ, h⟩ ⟨N', χ', h'⟩ e
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj e
  obtain rfl := eq_of_heq e2
  rfl
end HostParam.Seam
