-- Prove2me | solution 1 for GlobalTheory.Published.UnitaryFiniteCovolume.of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:07.510917+00:00
-- url     : https://prove2.me/submissions/780e6a8f-eee2-4356-8f8c-67bb04dd217e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
import Theorems.Thm_GlobalTheory_Published_UnitaryFiniteCovolume_compactSpace_of_definite

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
theorem _root_.solution {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r)
    (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (hH : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧
      ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ,
        (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
          (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
            (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  haveI := compactSpace_of_definite X hd H hH
  refine ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top, fun g =>
    ⟨1, ⟨fun x y => by simp, fun x => by simp⟩, g, Set.mem_univ _, fun τ => ?_⟩⟩
  simp
end GlobalTheory.Published.UnitaryFiniteCovolume
