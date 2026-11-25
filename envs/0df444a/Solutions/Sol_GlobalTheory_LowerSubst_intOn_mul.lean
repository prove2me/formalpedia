-- Prove2me | solution 1 for GlobalTheory.LowerSubst.intOn_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:32.119528+00:00
-- url     : https://prove2.me/submissions/ec486198-ce31-47b1-abc7-b69ad95186c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum


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
theorem _root_.solution (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f g : MvPowerSeries σ C}
    (hf : IntOn V P f) (hg : IntOn V P g) : IntOn V P (f * g) := by
  intro α hα
  rw [coeff_mul]
  refine VF.Ge.sum fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact VF.Ge.mul_int (hf _ (hP α _ (hx ▸ le_self_add) hα)) (hg _ (hP α _ (hx ▸ le_add_self) hα))
end GlobalTheory.LowerSubst
