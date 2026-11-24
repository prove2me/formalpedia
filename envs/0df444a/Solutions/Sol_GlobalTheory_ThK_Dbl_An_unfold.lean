-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:03.867483+00:00
-- url     : https://prove2.me/submissions/38d5d938-febb-4561-9f06-8ff9386e1fec

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_UnfoldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
namespace GlobalTheory.ThK.Dbl.An
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℂ} (hf : Integrable f μ) : ∫ x in D, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by
  rw [hD.integral_eq_tsum'' f hf]
  refine integral_tsum (fun γ => ((hf.comp_mul_left (γ : G)).aestronglyMeasurable).restrict) ?_
  have := hD.lintegral_eq_tsum'' fun x => ‖f x‖ₑ
  exact (this ▸ hf.2.ne :)
end GlobalTheory.ThK.Dbl.An
