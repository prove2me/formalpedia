-- Prove2me | solution 1 for GlobalTheory.LowerSubst.intOn_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:57.649409+00:00
-- url     : https://prove2.me/submissions/2b117b03-b0d0-41e2-8dee-8e126be4719e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSet
import Theorems.Thm_GlobalTheory_LowerSubst_intOn_one
import Theorems.Thm_GlobalTheory_LowerSubst_intOn_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.LowerSubst
open MvPowerSeries
variable {C : Type} [Field C] (V : VF C) {σ : Type} (P : (σ →₀ ℕ) → Prop)
namespace GlobalTheory.LowerSubst
theorem _root_.solution (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f : MvPowerSeries σ C} (hf : IntOn V P f)
    (n : ℕ) : IntOn V P (f ^ n) := by
  induction n with
  | zero => simpa using intOn_one V P
  | succ n ih => rw [pow_succ]; exact intOn_mul V P hP ih hf
end GlobalTheory.LowerSubst
