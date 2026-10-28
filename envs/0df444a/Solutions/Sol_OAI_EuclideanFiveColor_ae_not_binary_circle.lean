-- Prove2me | solution 1 for OAI.EuclideanFiveColor.ae_not_binary_circle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:57:48.505605+00:00
-- url     : https://prove2.me/submissions/ad00c096-4423-4cf3-a824-370f675a7e54

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_binary_centers_separated

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryPalettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma binary_centers_countable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (i j : Fin k) : {x | BinaryCenter c hc x i j}.Countable := by
  obtain ⟨δ,hδ,hsep⟩ := binary_centers_separated c hc hw
  have hp : {x | BinaryCenter c hc x i j}.PairwiseDisjoint (fun x => Metric.ball x (δ/2)) := by
    intro x hx z hz hne
    change Disjoint (Metric.ball x (δ/2)) (Metric.ball z (δ/2))
    rw [Set.disjoint_left]
    intro w hwx hwz
    have := dist_triangle x w z
    have hxw : dist x w < δ/2 := by simpa only [Metric.mem_ball,dist_comm] using hwx
    have hwz' : dist w z < δ/2 := hwz
    have := hsep x z i j hx hz hne
    linarith
  exact hp.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun x _ => ⟨x,Metric.mem_ball_self (by linarith)⟩)
lemma ae_not_binary_circle_oai {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℂ) (i j : Fin k) : ∀ᵐ t ∂angularMeasure, ¬ BinaryCenter c hc (x+direction t) i j := by
  have hi : Function.Injective (fun t => x+direction t) := by
    intro a b hab
    exact AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0)
      (Subtype.ext (add_left_cancel hab))
  have hn := ((binary_centers_countable c hc hw i j).preimage hi).measure_zero angularMeasure
  exact (measure_eq_zero_iff_ae_notMem).mp hn
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.ae_not_binary_circle_oai := @OAI.EuclideanFiveColor.ae_not_binary_circle_oai
