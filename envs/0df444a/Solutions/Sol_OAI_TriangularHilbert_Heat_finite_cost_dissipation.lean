-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.finite_cost_dissipation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:35:04.512647+00:00
-- url     : https://prove2.me/submissions/fae180e7-6c7c-4f9b-8ad1-f96e6de74715

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
open MatrixEnergy
open scoped BigOperators


theorem solution (α : Three → ℝ) (hα : ∀ w, 0 ≤ α w)
    (K : Three → Three → ℝ) (Z : Three → ℝ) (hK : ∀ v w, 0 ≤ K v w)
    (hrow : ∀ v, 2*Z v ≤ ∑ w, if w = v then 0 else K v w)
    (hcol : ∀ w, (∑ v, if v = w then 0 else K v w) ≤ Real.sqrt 2 * K w w) :
    (∑ v, ((∑ w, α w)*Z v - (∑ w, α w*K v w))) ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w))*K w w := by
  set S := ∑ w, α w with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg (fun w _ => hα w)
  have key : ∀ w, (S/2 - α w) * (∑ v, if v = w then 0 else K v w) ≤ (Real.sqrt 2 * max 0 (S/2-α w)) * K w w := by
    intro w
    have hC : 0 ≤ ∑ v, if v = w then 0 else K v w :=
      Finset.sum_nonneg (fun v _ => by split_ifs <;> simp [hK])
    calc (S/2 - α w) * (∑ v, if v = w then 0 else K v w)
        ≤ max 0 (S/2-α w) * (∑ v, if v = w then 0 else K v w) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hC
      _ ≤ max 0 (S/2-α w) * (Real.sqrt 2 * K w w) :=
          mul_le_mul_of_nonneg_left (hcol w) (le_max_left _ _)
      _ = _ := by ring
  have hr : ∀ v, S * Z v ≤ S/2 * ∑ w, if w = v then 0 else K v w := by
    intro v; nlinarith [hrow v]
  have k0 := key 0; have k1 := key 1; have k2 := key 2
  have r0 := hr 0; have r1 := hr 1; have r2 := hr 2
  simp only [Fin.sum_univ_three, Fin.isValue] at k0 k1 k2 r0 r1 r2 hSdef ⊢
  simp at k0 k1 k2 r0 r1 r2
  clear_value S
  linarith

