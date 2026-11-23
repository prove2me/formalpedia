-- Prove2me | solution 1 for GlobalTheory.SBConv.eventually_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:16.59048+00:00
-- url     : https://prove2.me/submissions/2413b442-ed1d-4722-9c96-edb3dd21324e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.SBConv
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
namespace GlobalTheory.SBConv
theorem _root_.solution {F : G → ℂ} (hF : F ∈ SB G) :
    ∀ᶠ x in nhds (0 : G), ∀ g, F (g - x) = F g := by
  have hlc : IsLocallyConstant F := hF.1
  have hK : IsCompact (tsupport F) := hF.2
  have hz : ∀ z, z ∉ tsupport F → F z = 0 := fun z hz => by
    by_contra h
    exact hz (subset_tsupport F h)
  have step : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - x) = F y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hy := hlc.eventually_eq y
    have h1 : Filter.Tendsto (fun p : G × G => p.2 - p.1) (nhds ((0 : G), y)) (nhds y) := by
      simpa using (continuous_snd.tendsto ((0 : G), y)).sub (continuous_fst.tendsto ((0 : G), y))
    have h2 : Filter.Tendsto (fun p : G × G => p.2) (nhds ((0 : G), y)) (nhds y) :=
      continuous_snd.tendsto _
    filter_upwards [h1.eventually hy, h2.eventually hy] with p hp1 hp2
    exact hp1.trans hp2.symm
  have step' : ∀ᶠ x in nhds (0 : G), ∀ y ∈ tsupport F, F (y - -x) = F y :=
    (continuous_neg.tendsto' (0 : G) 0 neg_zero).eventually step
  filter_upwards [step, step'] with x hx hx' g
  by_cases hg : g ∈ tsupport F
  · exact hx g hg
  · rw [hz g hg]
    by_cases hg' : g - x ∈ tsupport F
    · have h := hx' (g - x) hg'
      rw [sub_neg_eq_add, sub_add_cancel, hz g hg] at h
      exact h.symm
    · exact hz _ hg'
end GlobalTheory.SBConv
