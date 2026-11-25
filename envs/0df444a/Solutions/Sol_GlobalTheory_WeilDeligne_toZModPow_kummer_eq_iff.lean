-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.toZModPow_kummer_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:33.434904+00:00
-- url     : https://prove2.me/submissions/49a36f33-4c11-4e0d-8994-724091a4a409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Theorems.Thm_GlobalTheory_WeilDeligne_unityPow_eq_iff

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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable (l : ℕ) [Fact l.Prime]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (a : Eˣ) (σ τ : G E Ω) (n : ℕ) :
    PadicInt.toZModPow n (kummer l a σ) = PadicInt.toZModPow n (kummer l a τ) ↔
      σ (rootOf Ω l (a : E) n) = τ (rootOf Ω l (a : E) n) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  rw [kummer_spec, kummer_spec, mul_left_inj' (rootOf_ne_zero l a.ne_zero n)]
  exact (unityPow_eq_iff Ω l).symm
end GlobalTheory.WeilDeligne
