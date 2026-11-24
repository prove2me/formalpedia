-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HaarFactor.ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:18.697122+00:00
-- url     : https://prove2.me/submissions/844c3091-d52f-4fb8-9958-8bb2612f7e81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (U : Set A).indicator (fun _ => (1 : ℂ)) ∈ SB A := by
  have hcl : IsClopen (U : Set A) := ⟨U.isClosed_of_isOpen hUo, hUo⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hUc fun y hy => Set.indicator_of_notMem hy _⟩
  by_cases hx : x ∈ (U : Set A)
  · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
  · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
end GlobalTheory.SplitWeil.HaarFactor
