-- Prove2me | solution 1 for OAI.TriangularHilbert.intInterval_sum_fin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:34:23.791039+00:00
-- url     : https://prove2.me/submissions/589dc9fe-3931-49c9-8238-b60fe0b71d59

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

open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution (n : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ intInterval n N, f m) = ∑ i : Fin (2*N+1), f (n-(N:ℤ)+(i:ℕ)) := by
  rw [intInterval, Fin.sum_univ_eq_sum_range (fun i => f (n-(N:ℤ)+(i:ℕ))) (2*N+1)]
  refine Finset.sum_nbij' (fun m => (m - (n-N)).toNat) (fun i => n-N+i) ?_ ?_ ?_ ?_ ?_
  · intro m hm; simp only [Finset.mem_coe, Finset.mem_Icc] at hm; simp only [Finset.mem_coe, Finset.mem_range]; omega
  · intro i hi; simp at hi ⊢; omega
  · intro m hm; simp at hm ⊢; omega
  · intro i hi; simp
  · intro m hm; simp only [Finset.mem_Icc] at hm; congr 1; omega

