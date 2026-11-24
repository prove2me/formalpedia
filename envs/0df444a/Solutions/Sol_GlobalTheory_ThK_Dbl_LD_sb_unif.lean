-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:20.607586+00:00
-- url     : https://prove2.me/submissions/6fd57513-0e4d-4d5f-b50b-2c889cacb77f

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
theorem _root_.solution {X P : Type} [TopologicalSpace X] [TopologicalSpace P] {φ : X → ℂ} (hφ : φ ∈ SB X) (a : P → X → X) (p : P)
    (ha : Continuous fun z : P × X => a z.1 z.2) (h0 : ∀ x, a p x = x) :
    ∀ᶠ k in 𝓝 p, ∀ x ∈ tsupport φ, φ (a k x) = φ x := by
  apply IsCompact.eventually_forall_of_forall_eventually hφ.2
  intro y _
  have e := hφ.1.eventually_eq y
  have t1 : Tendsto (fun z : P × X => a z.1 z.2) (𝓝 (p, y)) (𝓝 y) := by simpa [h0] using ha.tendsto (p, y)
  filter_upwards [t1.eventually e, (continuous_snd.tendsto (p, y)).eventually e] with z h1 h2
  rw [h1, h2]
end GlobalTheory.ThK.Dbl.LD
