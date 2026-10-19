-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.continuous_heatMask
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:33:04.567978+00:00
-- url     : https://prove2.me/submissions/c8a369fc-b267-4e40-a164-25e2f47fc37e

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι uE
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
theorem solution {E : Type uE} [TopologicalSpace E] {r : E → Three → ι → ℝ}
    (hr : ∀ w j, Continuous (fun x => r x w j)) : Continuous (fun x => heatMask (r x)) := by
  unfold heatMask blockD
  refine continuous_pi fun ai => continuous_pi fun bj => ?_
  obtain ⟨a, i⟩ := ai; obtain ⟨b, j⟩ := bj
  show Continuous fun x => Matrix.diagonal (fun w => Matrix.diagonal (fun i => ((r x w i : ℝ) : ℂ))) a b i j
  by_cases hab : a = b
  · subst hab; simp only [Matrix.diagonal_apply_eq]
    by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq]; exact Complex.continuous_ofReal.comp (hr _ _)
    · simp only [Matrix.diagonal_apply_ne _ hij]; exact continuous_const
  · simp only [Matrix.diagonal_apply_ne _ hab]; exact continuous_const

