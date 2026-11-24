-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_chart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:55.699572+00:00
-- url     : https://prove2.me/submissions/e28498e4-484e-4dc7-9e56-29426eb59dee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {U : Set X} {T : Set Y} (hU : IsOpen U)
    {e : X → Y} {r : Y → X} (ce : ContinuousOn e U) (cr : ContinuousOn r T) (hre : ∀ x ∈ U, r (e x) = x)
    (hr : ∀ y ∈ T, r y ∈ U) {F : Y → ℂ} (hF : F ∈ SB Y) (hT : ∀ y ∉ T, F y = 0) {G : X → ℂ}
    (h1 : ∀ x ∈ U, G x = F (e x)) (h0 : ∀ x ∉ U, G x = 0) : G ∈ SB X := by
  have hcl : IsClosed (Function.support F) := (hF.1.isClopen_fiber 0).compl.isClosed
  have hc : IsCompact (Function.support F) := hF.2.of_isClosed_subset hcl subset_closure
  have hsub : Function.support F ⊆ T := fun y hy => by_contra fun h => hy (hT y h)
  have hC : IsCompact (r '' Function.support F) := hc.image_of_continuousOn (cr.mono hsub)
  have hz : ∀ x ∉ r '' Function.support F, G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [h1 x hxU]; exact by_contra fun h => hx ⟨e x, h, hre x hxU⟩
    · exact h0 x hxU
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro hC hz⟩
  by_cases hxU : x ∈ U
  · filter_upwards [(ce.continuousAt (hU.mem_nhds hxU)).eventually (hF.1.eventually_eq (e x)), hU.mem_nhds hxU] with y a b
    rw [h1 y b, h1 x hxU, a]
  · have : x ∉ r '' Function.support F := by rintro ⟨y, hy, rfl⟩; exact hxU (hr y (hsub hy))
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds this] with y hy
    rw [hz y hy, h0 x hxU]
end GlobalTheory.ThK.Dbl.LD
