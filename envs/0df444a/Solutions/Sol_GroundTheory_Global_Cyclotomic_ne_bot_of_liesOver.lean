-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.ne_bot_of_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:13.819406+00:00
-- url     : https://prove2.me/submissions/4ce1da9e-7757-442b-932a-d456477db183

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
omit [P.IsPrime]
include hp
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : P ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p : ℤ)})
    (by simpa using hp.out.ne_zero) P
end GroundTheory.Global.Cyclotomic
