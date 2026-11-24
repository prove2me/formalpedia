-- Prove2me | solution 1 for GlobalTheory.BorelUMod.mem_unipLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:35.285921+00:00
-- url     : https://prove2.me/submissions/a2f07c33-081c-4ed4-bc38-0c55bc990e91

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
theorem _root_.solution {σ : L →+* L}
    {hσ : ∀ x, Valued.v (σ x) = Valued.v x} {c : Fin n → Fin n → ℤ}
    {hc : _root_.GlobalTheory.BorelUMod.IsWeight c} {u : (_root_.GlobalTheory.LGrp.borelU σ n).U} :
    u ∈ _root_.GlobalTheory.BorelUMod.unipLat hσ hc ↔
      (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ _root_.GlobalTheory.BorelUMod.upLat L c :=
  Iff.rfl
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
