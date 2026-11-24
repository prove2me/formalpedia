-- Prove2me | solution 1 for GlobalTheory.Serre.finrank_fractionalIdeal_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:38.94594+00:00
-- url     : https://prove2.me/submissions/5fb7a213-c2ca-4179-84d2-fe7c6dbe89f2

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
omit [CharZero k]
namespace GlobalTheory.Serre
theorem _root_.solution {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (hI : I ≠ 0) : Module.finrank (𝓞 K) I = Module.finrank K E := by
  have : Module.Finite (𝓞 E) I :=
    Module.Finite.iff_fg.mpr (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)
  have : Module.Finite (𝓞 K) I := Module.Finite.trans (𝓞 E) I
  have : Nontrivial I :=
    Submodule.nontrivial_iff_ne_bot.mpr (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  obtain ⟨x, hx⟩ := exists_ne (0 : (I : Submodule (𝓞 E) E))
  refine le_antisymm (Module.finrank_le_of_rank_le ?_) ?_
  · rw [Module.finrank_eq_rank, IsFractionRing.rank_right_eq (𝓞 K) K E]
    exact Submodule.rank_le ((I : Submodule (𝓞 E) E).restrictScalars (𝓞 K))
  · rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E]
    exact LinearMap.finrank_le_finrank_of_injective
      (f := (LinearMap.toSpanSingleton (𝓞 E) I x).restrictScalars (𝓞 K)) (smul_left_injective _ hx)
end GlobalTheory.Serre
