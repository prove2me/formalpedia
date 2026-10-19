-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.finite_variance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:31:26.980685+00:00
-- url     : https://prove2.me/submissions/c882fccd-bae8-452e-a1f9-80d24093f08e

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution (σ : Three → ℝ) (hσ : ∀ w, 0 < σ w) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ (∀ w, a ≤ σ w) ∧ (∀ w, σ w ≤ b) := by
  refine ⟨Finset.univ.inf' Finset.univ_nonempty σ, Finset.univ.sup' Finset.univ_nonempty σ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty σ
    rw [hw]; exact hσ w
  · exact (Finset.inf'_le _ (Finset.mem_univ 0)).trans (Finset.le_sup' _ (Finset.mem_univ 0))
  · intro w; exact Finset.inf'_le _ (Finset.mem_univ w)
  · intro w; exact Finset.le_sup' _ (Finset.mem_univ w)

