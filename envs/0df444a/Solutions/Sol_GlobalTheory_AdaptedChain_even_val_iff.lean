-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.even_val_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:32.695851+00:00
-- url     : https://prove2.me/submissions/138a26c8-88b3-43d2-8167-a4ec6c1e6fae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d) + 1).val ↔ ¬ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : a + ((2 * s : ℕ) : ZMod d) + 1 = ((a.val + 2 * s + 1 : ℕ) : ZMod d) := by
    push_cast; simp
  rw [e, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2]
  omega
end GlobalTheory.AdaptedChain
