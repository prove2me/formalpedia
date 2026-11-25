-- Prove2me | solution 1 for GlobalTheory.LowerSubst.intOn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:58.408452+00:00
-- url     : https://prove2.me/submissions/72c69808-3dfb-4f51-b04c-eadfb5dd9b8e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSet
import Theorems.Thm_GlobalTheory_LowerSubst_intOn_one
import Theorems.Thm_GlobalTheory_LowerSubst_intOn_mul

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
theorem _root_.solution (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ C) (h : ∀ i ∈ s, IntOn V P (f i)) : IntOn V P (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOn V P) (fun _ _ => intOn_mul V P hP) (intOn_one V P) h
end GlobalTheory.LowerSubst
