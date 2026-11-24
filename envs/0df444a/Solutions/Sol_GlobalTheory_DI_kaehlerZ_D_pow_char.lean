-- Prove2me | solution 1 for GlobalTheory.DI.kaehlerZ_D_pow_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:09:23.568664+00:00
-- url     : https://prove2.me/submissions/97f462da-1650-420f-8925-1012d6f9ae37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtDAlgebraMapPowCharMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
namespace GlobalTheory.DI
theorem _root_.solution (c : K) : KaehlerDifferential.D ℤ K (c ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
end GlobalTheory.DI
