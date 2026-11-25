-- Prove2me | solution 1 for GlobalTheory.Published.UnitaryFiniteCovolume.exists_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:05.414819+00:00
-- url     : https://prove2.me/submissions/35efbcbe-0bb9-4995-8300-bfb11e5cd0d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
import Theorems.Thm_GlobalTheory_UnitaryFrames_unitary_group_frames


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.UnitaryFiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.UnitaryFiniteCovolume
theorem _root_.solution {r : ℕ} (X : Data E r) :
    ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧
      ∃ (_ : MeasurableSpace H) (_ : BorelSpace H) (ν : Measure H), ν.IsHaarMeasure := by
  obtain ⟨H, hH⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.1 r X
  haveI := (GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH).1
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  exact ⟨H, hH, inferInstance, inferInstance, Measure.haar, inferInstance⟩
end GlobalTheory.Published.UnitaryFiniteCovolume
