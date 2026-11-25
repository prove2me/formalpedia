-- Prove2me | solution 1 for GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:50.949864+00:00
-- url     : https://prove2.me/submissions/ec4389d7-48d8-4bcb-8283-232c180dfd6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffIntegralOnExponentsSubstOfLowerSetStatement
import Theorems.Thm_GlobalTheory_LowerSubst_subst_int_on_lower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  first | exact @GlobalTheory.LowerSubst.subst_int_on_lower | exact GlobalTheory.LowerSubst.subst_int_on_lower | (intros; apply GlobalTheory.LowerSubst.subst_int_on_lower <;> assumption)
end _root_.GlobalTheory.T
