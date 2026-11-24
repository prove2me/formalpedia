-- Prove2me | solution 1 for GlobalTheory.SplitWeil.exists_isSelfDual_of_hasConductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:10.865853+00:00
-- url     : https://prove2.me/submissions/340476b5-2bb5-4175-9c54-e15b4bb49f9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Theorems.Thm_GlobalTheory_SplitWeil_isSelfDual_iff_vol
import Theorems.Thm_GlobalTheory_SplitWeil_exists_isUnitVol
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}
namespace GlobalTheory.SplitWeil
theorem _root_.solution (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']
end GlobalTheory.SplitWeil
