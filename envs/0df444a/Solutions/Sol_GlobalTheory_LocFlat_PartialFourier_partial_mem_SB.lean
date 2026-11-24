-- Prove2me | solution 1 for GlobalTheory.LocFlat.PartialFourier.partial_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:39:02.984846+00:00
-- url     : https://prove2.me/submissions/96930de2-52c5-42f7-9afb-62d9729fdf89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialFourierInversion
import Theorems.Thm_GlobalTheory_LocFlat_PartialFourier_eventually_add_invariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PartialFourier
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
omit [BorelSpace k]
namespace GlobalTheory.LocFlat.PartialFourier
theorem _root_.solution {I J : Type} [Fintype I] [Fintype J] (ν : Measure k) {f : (I → k) × (J → k) → ℂ}
    (hf : f ∈ SB ((I → k) × (J → k))) :
    (fun x₁ : I → k => ∫ y : J → k, f (x₁, y) ∂(Measure.pi fun _ => ν)) ∈ SB (I → k) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_, ?_⟩
  · have h2 : Filter.Tendsto (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) (𝓝 x) (𝓝 0) := by
      have : Continuous (fun z : I → k => ((z - x, 0) : (I → k) × (J → k))) := by fun_prop
      convert this.tendsto x using 2
      simp only [sub_self]
      rfl
    filter_upwards [h2.eventually (eventually_add_invariant hf)] with z hz
    congr 1
    funext y
    have := hz (x, y)
    simpa using this
  · refine HasCompactSupport.intro (hf.2.image continuous_fst) fun x hx => ?_
    have : ∀ y, f (x, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [this]
end GlobalTheory.LocFlat.PartialFourier
