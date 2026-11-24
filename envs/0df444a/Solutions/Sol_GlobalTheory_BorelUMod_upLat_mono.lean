-- Prove2me | solution 1 for GlobalTheory.BorelUMod.upLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:28.141808+00:00
-- url     : https://prove2.me/submissions/3812180b-13df-4973-a5c1-404182ef9d2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


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
theorem _root_.solution {c C : Fin n → Fin n → ℤ}
    (h : ∀ i j, i < j → c i j ≤ C i j) :
    _root_.GlobalTheory.BorelUMod.upLat L C ≤ _root_.GlobalTheory.BorelUMod.upLat L c :=
  fun _ hX => ⟨hX.1, fun i j hij =>
    (hX.2 i j hij).trans (WithZero.exp_le_exp.2 (neg_le_neg (h i j hij)))⟩
end _root_.GlobalTheory.BorelUMod
end GlobalTheory.BorelUMod
