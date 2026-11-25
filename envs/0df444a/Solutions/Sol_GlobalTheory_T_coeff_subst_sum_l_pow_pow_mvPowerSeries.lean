-- Prove2me | solution 1 for GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:43.371949+00:00
-- url     : https://prove2.me/submissions/b05dd449-254b-4af5-a5d8-cca18c621adf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffSubstSumLPowPowMvPowerSeries
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffSubstSumLPowPowMvPowerSeriesStatement
import Theorems.Thm_GlobalTheory_LogSubst_coeff_subst_sum_pow_pow


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
theorem _root_.solution : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  first | exact @GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | exact GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | (intros; apply GlobalTheory.LogSubst.coeff_subst_sum_pow_pow <;> assumption)
end _root_.GlobalTheory.T
