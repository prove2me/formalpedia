-- Prove2me | solution 1 for OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:23:42.09491+00:00
-- url     : https://prove2.me/submissions/ec9f2952-16d7-4ad2-a43c-088f86e0d60d

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003
import Theorems.Thm_OAI_StrictHotSpots_InteriorBoundarySign_exists_boundary_pos

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorBoundarySign

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.InteriorBoundarySign
open StrictHotSpots.BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
lemma eigen_neg (hu : InInteriorNeumannEigenspace Ω u) : InInteriorNeumannEigenspace Ω (-u) := by
  have hg : gradient (-u) = -gradient u := by
    funext x
    simp only [gradient,Pi.neg_apply,fderiv_neg,map_neg]
  refine ⟨hu.1.neg,?_,?_,?_⟩
  · simpa only [hg,neg_one_smul] using hu.2.1.smul (-1)
  · simp only [Pi.neg_apply,integral_neg,hu.2.2.1,neg_zero]
  · intro v g hv
    simp only [hg,Pi.neg_apply,inner_neg_left,neg_mul,integral_neg]
    rw [hu.2.2.2 v g hv]
    ring
lemma exists_boundary_neg_oai (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω)) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∃ x ∈ frontier Ω, u x < 0 := by
  have hn : ∃ x ∈ Ω, (-u) x ≠ 0 := by
    obtain ⟨x,hx,hux⟩ := hne
    exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_ne_zero] using hux⟩
  obtain ⟨x,hx,hux⟩ := exists_boundary_pos ho hbound (eigen_neg hu) hc.neg hn
  exact ⟨x,hx,by simpa only [Pi.neg_apply,neg_pos] using hux⟩

end StrictHotSpots.InteriorBoundarySign
end
end ActualInteriorBoundarySign


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg_oai := @OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_neg_oai
