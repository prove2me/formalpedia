-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isUnitVol_iff_isSelfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:11.755298+00:00
-- url     : https://prove2.me/submissions/3f2dd11c-851e-42b8-b17e-9fbab7bf382e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Theorems.Thm_GlobalTheory_SplitWeil_isSelfDual_iff_vol
import Theorems.Thm_GlobalTheory_SplitWeil_isSelfDual_of_isUnitVol
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_one


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
theorem _root_.solution (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · exact isSelfDual_of_isUnitVol ν h
  · intro hsd
    have := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩
end GlobalTheory.SplitWeil
