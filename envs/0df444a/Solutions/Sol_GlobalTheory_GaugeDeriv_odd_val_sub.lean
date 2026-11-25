-- Prove2me | solution 1 for GlobalTheory.GaugeDeriv.odd_val_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:06.019807+00:00
-- url     : https://prove2.me/submissions/0853ef9e-8bc6-4580-9e6e-247d409eaacf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivLeafGaugeEqPairingAddIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.GaugeDeriv
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {ι ι' : Type} [Fintype ι] [Fintype ι']
variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]
namespace GlobalTheory.GaugeDeriv
theorem _root_.solution {d : ℕ} [NeZero d] (a : ZMod d) {i : ℕ} (hi : Odd i) (hid : i < d) :
    Odd (a + (i : ZMod d) - a).val := by
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hid]
  exact hi
end GlobalTheory.GaugeDeriv
