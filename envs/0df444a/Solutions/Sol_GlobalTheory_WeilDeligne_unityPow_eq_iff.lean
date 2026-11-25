-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.unityPow_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:05:49.892271+00:00
-- url     : https://prove2.me/submissions/b0d21662-fc86-4d0c-83fc-66ce4ee797d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
variable (Ω) [CharZero Ω]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {n : ℕ} {c d : ℤ_[l]} :
    unityPow Ω l n c = unityPow Ω l n d ↔ PadicInt.toZModPow n c = PadicInt.toZModPow n d := by
  conv_lhs => rw [unityPow.eq_def Ω l n d]
  rw [unityPow_eq_pow_iff, ZMod.natCast_zmod_val]
end GlobalTheory.WeilDeligne
