-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.flow_limit_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:08:55.302847+00:00
-- url     : https://prove2.me/submissions/963e695e-9547-4fa1-b7ca-42a9fbdd366f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MultiwayGap2325_Main_Supplement_FluxJumps
import Theorems.Thm_MultiwayGap2325_Main_Supplement_summation_over_faces
import Theorems.Thm_MultiwayGap2325_Main_Supplement_one_face
import Theorems.Thm_MultiwayGap2325_Main_Supplement_expected_cost
import Theorems.Thm_MultiwayGap2325_Main_non_opposite_reduction
import Theorems.Thm_MultiwayGap2325_Main_approximationFactor_ge_one_zero

open MeasureTheory Filter Set
open MultiwayGap2325.Main MultiwayGap2325.Main.Supplement
open scoped BigOperators ENNReal

theorem solution (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) (D : FlowData q)
    (hD : IsFlowInstance T D) (hL : 0 < totalL T D.weighting) :
    ∃ g : ℝ, Tendsto gapSequence atTop (nhds g) ∧
      (totalB T D.weighting - totalR T D) / totalL T D.weighting ≤ g := by
  have hflow : ∀ (Ξ : Type) [MeasurableSpace Ξ]
      (P : Measure Ξ) [IsProbabilityMeasure P]
      (C : RandomNonOppositeCut q Ξ P) (α : ℝ),
      HasApproximationFactor C α →
        (totalB T D.weighting - totalR T D) / totalL T D.weighting ≤ α := by
    intro Ξ _ P _ C α hα
    let J : Ξ → ℝ := fun ξ => totalFluxJump T D (fun x => C.labeling (ξ, x))
    let A : Ξ → ℝ := fun ξ => totalRealFaceCost T D.weighting (fun x => C.labeling (ξ, x))
    let E : Ξ → ℝ := fun ξ => realTerminalCost T D.weighting (fun x => C.labeling (ξ, x))
    obtain ⟨hJi, hAi, hJA⟩ := one_face q hq T hT0 hT1 D hD Ξ P C α hα
    obtain ⟨hcmeas, hcfin, hclint, hcint, hEi, hsplit, hupper⟩ :=
      expected_cost q hq T hT0 hT1 D hD Ξ P C α hα
    have hJint : Integrable J P := by
      dsimp [J, totalFluxJump]
      exact integrable_finset_sum _ (fun S _ => hJi S)
    have hAint : Integrable A P := by
      dsimp [A, totalRealFaceCost]
      exact integrable_finset_sum _ (fun S _ => hAi S)
    have hJAint : (∫ ξ, J ξ ∂P) ≤ ∫ ξ, A ξ ∂P := by
      have hJsum : (∫ ξ, J ξ ∂P) = ∑ S : Face q,
          ∫ ξ, fluxJump T D S (fun x => C.labeling (ξ, x)) ∂P := by
        dsimp [J, totalFluxJump]
        exact integral_finset_sum _ (fun S _ => hJi S)
      have hAsum : (∫ ξ, A ξ ∂P) = ∑ S : Face q,
          ∫ ξ, realFaceCost T D.weighting S (fun x => C.labeling (ξ, x)) ∂P := by
        dsimp [A, totalRealFaceCost]
        exact integral_finset_sum _ (fun S _ => hAi S)
      rw [hJsum, hAsum]
      exact Finset.sum_le_sum (fun S _ => hJA S)
    have hdet : ∀ ξ, totalB T D.weighting - totalR T D ≤ J ξ + E ξ := by
      intro ξ
      exact summation_over_faces q hq T hT0 hT1 D hD Ξ P C ξ
    have hlowerJE : totalB T D.weighting - totalR T D ≤
        (∫ ξ, J ξ ∂P) + ∫ ξ, E ξ ∂P := by
      rw [← integral_add hJint hEi]
      simpa using integral_mono (integrable_const _) (hJint.add hEi) hdet
    have hsplitInt : ∫ ξ, (cutCost T D.weighting (fun x => C.labeling (ξ, x))).toReal ∂P =
        (∫ ξ, A ξ ∂P) + ∫ ξ, E ξ ∂P := by
      rw [← integral_add hAint hEi]
      exact integral_congr_ae hsplit
    have hlower : totalB T D.weighting - totalR T D ≤
        ∫ ξ, (cutCost T D.weighting (fun x => C.labeling (ξ, x))).toReal ∂P := by
      rw [hsplitInt]
      exact hlowerJE.trans (add_le_add hJAint le_rfl)
    apply (div_le_iff₀ hL).2
    exact hlower.trans hupper
  by_cases hb : 0 < (totalB T D.weighting - totalR T D) / totalL T D.weighting
  · obtain ⟨g, hg, hbg, _⟩ := non_opposite_reduction q hq _ hb hflow
    exact ⟨g, hg, hbg⟩
  · have hone : ∀ (Ξ : Type) [MeasurableSpace Ξ]
        (P : Measure Ξ) [IsProbabilityMeasure P]
        (C : RandomNonOppositeCut q Ξ P) (α : ℝ),
        HasApproximationFactor C α → 1 ≤ α := by
      intro Ξ _ P _ C α hα
      exact approximationFactor_ge_one_zero q hq Ξ P C α hα
    obtain ⟨g, hg, h1g, _⟩ := non_opposite_reduction q hq 1 zero_lt_one hone
    refine ⟨g, hg, ?_⟩
    exact (le_of_not_gt hb).trans (zero_le_one.trans h1g)
