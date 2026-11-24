-- Prove2me | solution 1 for GlobalTheory.Serre.finrank_fractionalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:38.117015+00:00
-- url     : https://prove2.me/submissions/3080fbef-7681-4188-94c2-eaf85c836c79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedRingOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.Serre
open NumberField
variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]
omit [CharZero k] [NumberField K]
namespace GlobalTheory.Serre
theorem _root_.solution {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    Module.finrank (𝓞 E) I = 1 := by
  have h₁ : Module.finrank (𝓞 E) E = 1 := by
    rw [← IsFractionRing.finrank_right_eq (𝓞 E) E E, Module.finrank_self]
  have : Module.Finite (𝓞 E) I :=
    Module.Finite.iff_fg.mpr (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)
  have : Nontrivial I :=
    Submodule.nontrivial_iff_ne_bot.mpr (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  refine le_antisymm ?_ Module.finrank_pos
  refine Module.finrank_le_of_rank_le ((Submodule.rank_le (I : Submodule (𝓞 E) E)).trans ?_)
  rw [← IsFractionRing.rank_right_eq (𝓞 E) E E, Module.rank_self, Nat.cast_one]
end GlobalTheory.Serre
