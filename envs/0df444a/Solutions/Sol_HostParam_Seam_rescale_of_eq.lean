-- Prove2me | solution 1 for HostParam.Seam.rescale_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:27.668879+00:00
-- url     : https://prove2.me/submissions/b74a6701-6c0e-4607-a72d-4b57f6a06ca0

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
theorem _root_.solution {T : HostType} {T' : HType} (h : T.J = T'.J) (X : ℝ) : rescale T T' X = X := by
  have hJ : T.J ≠ 0 := (lt_of_lt_of_le one_pos T.one_le_J).ne'
  rw [rescale, ← h, div_self hJ, Real.rpow_one]
end HostParam.Seam
