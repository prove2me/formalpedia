-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:43.3868+00:00
-- url     : https://prove2.me/submissions/0f04b3ea-b146-43f9-ab24-7d2cca4d9b86

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ne_bot_of_liesOver

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
theorem _root_.solution : Finite (𝓞 K ⧸ P) :=
  have : NeZero P := ⟨ne_bot_of_liesOver p K P⟩
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne P)
end GroundTheory.Global.Cyclotomic
