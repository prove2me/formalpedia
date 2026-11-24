-- Prove2me | solution 1 for GlobalTheory.PartialIntegral.eventually_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:55.557812+00:00
-- url     : https://prove2.me/submissions/f1643e54-ce08-4bde-8970-cb63c1f28cf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocallyConstantPartial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.PartialIntegral
variable {Y B W : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [TopologicalSpace B] [T2Space B] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  (ν : Measure Y) [ν.IsAddHaarMeasure]
namespace GlobalTheory.PartialIntegral
theorem _root_.solution {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) :
    ∀ᶠ u in 𝓝 (0 : W), ∀ x, g (x + u) = g x := by
  have h : ∀ᶠ u in 𝓝 (0 : W), ∀ x ∈ tsupport g, g (x + u) = g x ∧ g (x - u) = g x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : W × W => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  filter_upwards [h] with u hu x
  by_cases hx : x ∈ tsupport g
  · exact (hu x hx).1
  · by_cases hx' : x + u ∈ tsupport g
    · have := (hu _ hx').2
      rw [add_sub_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
end GlobalTheory.PartialIntegral
