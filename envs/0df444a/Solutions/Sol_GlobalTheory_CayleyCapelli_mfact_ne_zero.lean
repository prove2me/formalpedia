-- Prove2me | solution 1 for GlobalTheory.CayleyCapelli.mfact_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:10.702686+00:00
-- url     : https://prove2.me/submissions/63dfb5c5-6200-4550-9dc2-551ab10a93c2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open GlobalTheory GlobalTheory.CayleyCapelli
open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing
variable {σ : Type} {C : Type} [Field C]
namespace GlobalTheory.CayleyCapelli
theorem _root_.solution [CharZero C] (A : σ →₀ ℕ) : (mfact A : C) ≠ 0 := by
  rw [Nat.cast_ne_zero, mfact, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
end GlobalTheory.CayleyCapelli
