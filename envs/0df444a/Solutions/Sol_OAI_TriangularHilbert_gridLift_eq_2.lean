-- Prove2me | solution 2 for OAI.TriangularHilbert.gridLift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:00:29.390315+00:00
-- url     : https://prove2.me/submissions/35103d52-291c-4517-a015-6ac9c1695b59

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GridCell.lean:L56-L86
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.gridLift_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell

-- ---- from OAI.Analysis.TriangularHilbert.GridCell ----
namespace OAI

universe uE uF

section
namespace TriangularHilbert
open MeasureTheory
open scoped BigOperators
noncomputable section

lemma gridCell_mem_iff {h x : ℝ} (hh : 0 < h) (i : ℤ) :
    x ∈ gridCell h i ↔ gridIndex h x = i := by
  unfold gridCell gridIndex
  rw [Int.floor_eq_iff]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    exact ⟨(le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hx.1),
      (div_lt_iff₀ hh).mpr (by simpa only [mul_comm] using hx.2)⟩
  · intro hx
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hh).mp hx.1,
      by simpa only [mul_comm] using (div_lt_iff₀ hh).mp hx.2⟩

lemma gridRect_mem_iff {h : ℝ} (hh : 0 < h) (z : ℝ×ℝ) (i j : ℤ) :
    z ∈ gridRect h i j ↔ gridIndex h z.1 = i ∧ gridIndex h z.2 = j := by
  exact and_congr (gridCell_mem_iff hh i) (gridCell_mem_iff hh j)

lemma gridLift_eq {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → D → E) (z : ℝ×ℝ) : gridLift D h f z =
      if hi : gridIndex h z.1 ∈ D then if hj : gridIndex h z.2 ∈ D then
        f ⟨gridIndex h z.1,hi⟩ ⟨gridIndex h z.2,hj⟩ else 0 else 0 := by
  classical
  unfold gridLift
  simp_rw [Set.indicator_apply,gridRect_mem_iff hh]
  split_ifs with hi hj
  · rw [Finset.sum_eq_single (⟨gridIndex h z.1,hi⟩:D)]
    · rw [Finset.sum_eq_single (⟨gridIndex h z.2,hj⟩:D)]
      · simp
      · intro j _ hj'
        have hne : gridIndex h z.2 ≠ (j:ℤ) := by intro he; exact hj' (Subtype.ext he.symm)
        simp only [hne,and_false,ite_false]
      · simp
    · intro i _ hi'
      have hne : gridIndex h z.1 ≠ (i:ℤ) := by intro he; exact hi' (Subtype.ext he.symm)
      simp only [hne,false_and,ite_false,Finset.sum_const_zero]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : gridIndex h z.2 ≠ (j:ℤ) := by intro he; exact hj (he ▸ j.property)
    simp only [hne,and_false,ite_false]
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hne : gridIndex h z.1 ≠ (i:ℤ) := by intro he; exact hi (he ▸ i.property)
    simp only [hne,false_and,ite_false]

end
end TriangularHilbert
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert
open MeasureTheory
open scoped BigOperators


theorem solution.{uE} : type_of% @_root_.OAI.TriangularHilbert.gridLift_eq.{uE} := @_root_.OAI.TriangularHilbert.gridLift_eq.{uE}
