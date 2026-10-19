-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.continuous_heatRow_param
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:00:06.437894+00:00
-- url     : https://prove2.me/submissions/0f2edd05-88b6-46f8-b962-38988e19af73

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι uE
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]


theorem solution {E : Type uE} [TopologicalSpace E]
    (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v : Three) :
    Continuous (fun t => rowStar (heatArray A h u (p t) (σ t)) v) := by
  have hdens : ∀ (w : Three) (c : ℝ), Continuous (fun t => density (σ t w) (c - p t w)) := by
    intro w c
    have hs : Continuous (fun t => σ t w) := (continuous_apply w).comp hσ
    have hp' : Continuous (fun t => p t w) := (continuous_apply w).comp hp
    unfold density
    refine Continuous.mul ?_ ?_
    · refine Continuous.inv₀ ?_ (fun t => ?_)
      · exact Real.continuous_sqrt.comp (continuous_const.mul hs)
      · have := hpos t w; positivity
    · refine Real.continuous_exp.comp (Continuous.div ?_ (continuous_const.mul hs) (fun t => ?_))
      · exact ((continuous_const.sub hp').pow 2).neg
      · have := hpos t w; positivity
  have hW : ∀ w i j, Continuous (fun t => heatArray A h u (p t) (σ t) w i j) := by
    intro w i j
    unfold heatArray heatWeights weightedArray weight
    refine Continuous.mul (Continuous.mul ?_ continuous_const) ?_
    · exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.mul (hdens w (u i))))
    · exact Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.mul (hdens (w+1) (u j))))
  have hT : Continuous (fun t => triangle (heatArray A h u (p t) (σ t))) := by
    refine continuous_pi fun ai => continuous_pi fun bj => ?_
    obtain ⟨a, i⟩ := ai; obtain ⟨b, j⟩ := bj
    show Continuous fun t => triangleBlocks (heatArray A h u (p t) (σ t)) a b i j
    fin_cases a <;> fin_cases b <;>
      simp only [triangleBlocks, Matrix.conjTranspose_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
        if_true, if_false, Fin.reduceFinMk, Fin.reduceEq, Matrix.zero_apply] <;>
      first
        | exact continuous_const
        | exact hW _ _ _
        | exact continuous_star.comp (hW _ _ _)
  unfold rowStar
  exact continuous_const.matrix_mul hT

