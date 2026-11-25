-- Prove2me | solution 1 for GlobalTheory.SplitWeil.selfDual_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:01.394322+00:00
-- url     : https://prove2.me/submissions/c31cdaa1-d73c-45d1-b8ec-a8e2130bc96a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSelfDualOfHasConductor
import Theorems.Thm_GlobalTheory_SplitWeil_isSelfDual_iff_vol
import Theorems.Thm_GlobalTheory_SplitWeil_exists_isSelfDual_of_hasConductor
import Theorems.Thm_GlobalTheory_SplitWeil_isUnitVol_iff_isSelfDual
import Theorems.Thm_GlobalTheory_SplitWeil_exists_hasConductor_of_continuous


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν
end GlobalTheory.SplitWeil
