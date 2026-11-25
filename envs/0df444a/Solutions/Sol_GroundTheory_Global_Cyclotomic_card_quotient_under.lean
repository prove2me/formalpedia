-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.card_quotient_under
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:11.430312+00:00
-- url     : https://prove2.me/submissions/fdb7202e-4e60-4512-8cad-c21561b3f65a

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
omit hp [NumberField K] [P.IsPrime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : Nat.card (ℤ ⧸ P.under ℤ) = p := by
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}),
    Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
end GroundTheory.Global.Cyclotomic
