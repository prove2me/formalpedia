-- Prove2me | solution 1 for GlobalTheory.BorelUMod.mem_skewJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:55.211835+00:00
-- url     : https://prove2.me/submissions/868ae99c-f712-405b-ab02-42d10da721ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
namespace _root_.GlobalTheory.BorelUMod
theorem _root_.solution {σ : L →+* L} {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.skewJ σ n ↔ _root_.GlobalTheory.BorelUMod.adjJ σ X = -X :=
  Iff.rfl
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
