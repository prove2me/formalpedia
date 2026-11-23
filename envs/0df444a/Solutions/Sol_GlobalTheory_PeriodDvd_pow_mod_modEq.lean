-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.pow_mod_modEq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:03.469871+00:00
-- url     : https://prove2.me/submissions/52a0a101-f598-49b9-85ed-348616311ac5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution (q d m : ℕ) (hq : 1 ≤ q) : q ^ (m % d) ≡ q ^ m [MOD q ^ d - 1] := by
  have h1 : q ^ d ≡ 1 [MOD q ^ d - 1] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq)).mpr dvd_rfl).symm
  conv_rhs => rw [← Nat.mod_add_div m d, pow_add, pow_mul]
  have := (h1.pow (m / d)).mul_left (q ^ (m % d))
  simpa using this.symm
end GlobalTheory.PeriodDvd
