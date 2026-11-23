-- Prove2me | solution 1 for GlobalTheory.BorelUMod.mem_upLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:55.417948+00:00
-- url     : https://prove2.me/submissions/95df44ae-f289-4351-b055-33f118953db7

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
namespace GlobalTheory.BorelUMod
namespace _root_.GlobalTheory.BorelUMod
theorem _root_.solution {c : Fin n → Fin n → ℤ}
    {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.upLat L c ↔
      (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j) :=
  Iff.rfl
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
