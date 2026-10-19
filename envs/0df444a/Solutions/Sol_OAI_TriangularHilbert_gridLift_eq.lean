-- Prove2me | solution 1 for OAI.TriangularHilbert.gridLift_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:47:51.698664+00:00
-- url     : https://prove2.me/submissions/067fece6-1e5b-4f4d-aa7b-c85fd1659c85

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

open OAI OAI.TriangularHilbert
universe uE uF
open MeasureTheory
open scoped BigOperators


theorem solution {D : Finset ℤ} {h : ℝ} (hh : 0 < h) {E : Type uE} [AddCommMonoid E]
    (f : D → D → E) (z : ℝ×ℝ) : gridLift D h f z =
      if hi : gridIndex h z.1 ∈ D then if hj : gridIndex h z.2 ∈ D then
        f ⟨gridIndex h z.1,hi⟩ ⟨gridIndex h z.2,hj⟩ else 0 else 0 := by
  have key : ∀ (i : ℤ) (x : ℝ), x ∈ gridCell h i ↔ gridIndex h x = i := by
    intro i x
    rw [gridCell, gridIndex, Set.mem_Ico, Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh]
    constructor <;> rintro ⟨a, b⟩ <;> constructor <;> push_cast at * <;> linarith
  unfold gridLift
  simp only [Set.indicator, gridRect, Set.mem_prod, key]
  split_ifs with hi hj
  · rw [Finset.sum_eq_single ⟨_, hi⟩, Finset.sum_eq_single ⟨_, hj⟩]
    · simp
    · intro b _ hb; rw [if_neg]; rintro ⟨-, h2⟩; exact hb (Subtype.ext h2.symm)
    · simp
    · intro b _ hb; refine Finset.sum_eq_zero fun c _ => ?_
      rw [if_neg]; rintro ⟨h1, -⟩; exact hb (Subtype.ext h1.symm)
    · simp
  · refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; rintro ⟨-, h2⟩; exact hj (h2 ▸ c.2)
  · refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
    rw [if_neg]; rintro ⟨h1, -⟩; exact hi (h1 ▸ b.2)

