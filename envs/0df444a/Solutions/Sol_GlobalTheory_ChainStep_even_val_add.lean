-- Prove2me | solution 1 for GlobalTheory.ChainStep.even_val_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:58.746936+00:00
-- url     : https://prove2.me/submissions/9e6e5645-610d-45b4-93db-d9fcc1101f25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal

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
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ChainStep
theorem _root_.solution {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d)).val ↔ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2,
    Nat.add_mod, Nat.mod_mod_of_dvd _ h2]
  simp
end GlobalTheory.ChainStep
