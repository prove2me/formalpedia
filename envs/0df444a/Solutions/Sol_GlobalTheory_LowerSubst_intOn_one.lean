-- Prove2me | solution 1 for GlobalTheory.LowerSubst.intOn_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:25.765602+00:00
-- url     : https://prove2.me/submissions/76730df1-b286-49b3-bf6d-15ba8ac5586f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
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
theorem _root_.solution : IntOn V P (1 : MvPowerSeries σ C) := by
  intro α _
  rw [coeff_one]
  split_ifs with h
  · exact VF.Ge.one
  · exact VF.Ge.zero 0
end GlobalTheory.LowerSubst
