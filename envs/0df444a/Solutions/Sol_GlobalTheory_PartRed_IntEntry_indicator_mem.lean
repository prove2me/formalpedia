-- Prove2me | solution 1 for GlobalTheory.PartRed.IntEntry.indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:59.590529+00:00
-- url     : https://prove2.me/submissions/ca4f415d-a180-4065-b211-c0d88c75939e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslation
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.IntEntry
namespace GlobalTheory.PartRed.IntEntry
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [Fintype Q] (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → ∀ (U : AddSubgroup k), IsOpen (U : Set k) → ∀ (e : R × Q) (a : k), Set.indicator {t : Matrix R Q k | t e.1 e.2 - a ∈ U} Φ ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ R Q _ _ Φ hΦ U hU e a
  have hc : Continuous fun t : Matrix R Q k => t e.1 e.2 - a := by fun_prop
  have hcl : IsClopen {t : Matrix R Q k | t e.1 e.2 - a ∈ U} :=
    ⟨(U.isClosed_of_isOpen hU).preimage hc, hU.preimage hc⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hΦ.2 fun y hy => ?_⟩
  · by_cases hx : x ∈ {t : Matrix R Q k | t e.1 e.2 - a ∈ U}
    · filter_upwards [hcl.isOpen.mem_nhds hx, hΦ.1.eventually_eq x] with z hz hz'
      exact (Set.indicator_of_mem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hz Φ).trans
        (hz'.trans (Set.indicator_of_mem hx Φ).symm)
    · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
      exact (Set.indicator_of_notMem (s := {t : Matrix R Q k | t e.1 e.2 - a ∈ U}) hz Φ).trans
        (Set.indicator_of_notMem hx Φ).symm
  · exact Set.indicator_apply_eq_zero.mpr fun _ => image_eq_zero_of_notMem_tsupport hy
end GlobalTheory.PartRed.IntEntry
