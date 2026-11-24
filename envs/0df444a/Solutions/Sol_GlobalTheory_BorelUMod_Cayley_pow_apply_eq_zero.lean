-- Prove2me | solution 1 for GlobalTheory.BorelUMod.Cayley.pow_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:28.851578+00:00
-- url     : https://prove2.me/submissions/d4031816-6d2d-41f6-adb3-e94aed7e686f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Theorems.Thm_GlobalTheory_StrictUpperNilpotent_pow_apply_eq_zero_of_strictUpper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod.Cayley
theorem _root_.solution {y : Matrix (Fin n) (Fin n) L} (hy : ∀ i j, j ≤ i → y i j = 0) (k : ℕ) :
    ∀ i j : Fin n, j.val < i.val + k → (y ^ k) i j = 0 := by
  first
  | exact @_root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
  | exact _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
  | (apply _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper ..)
end GlobalTheory.BorelUMod.Cayley
