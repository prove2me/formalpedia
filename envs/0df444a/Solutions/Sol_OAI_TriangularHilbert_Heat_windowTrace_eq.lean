-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.windowTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:58:22.608611+00:00
-- url     : https://prove2.me/submissions/15317863-38c9-4500-a61f-332f0c0269c3

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

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
universe uι
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
theorem h43_tr {κ : Type*} [Fintype κ] [DecidableEq κ] (d0 d1 d2 : κ → ℂ) (M0 M1 M2 : Matrix κ κ ℂ) :
    Matrix.trace (Matrix.diagonal d0 * M0 * Matrix.diagonal d1 * M1 * Matrix.diagonal d2 * M2) =
      ∑ i, ∑ j, ∑ k, d0 i * M0 i j * d1 j * M1 j k * d2 k * M2 k i := by
  rw [Matrix.mul_assoc (Matrix.diagonal d0 * M0), Matrix.mul_assoc (Matrix.diagonal d0 * M0 * _)]
  have e : ∀ (d : κ → ℂ) (M : Matrix κ κ ℂ), Matrix.diagonal d * M = Matrix.of (fun a b => d a * M a b) := by
    intro d M; ext a b; simp [Matrix.diagonal_mul]
  rw [e, e, e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem solution (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) :
    windowTrace A h u p s = ∑ i, ∑ j, ∑ k,
      (h^3:ℝ)* (A 0 i j*A 1 j k*A 2 k i) *
        ((oddWindow s (u i-p 0)*oddWindow s (u j-p 1)*oddWindow s (u k-p 2):ℝ):ℂ) := by
  have hs' : 0 < (11/10:ℝ)*s := by positivity
  have key : ∀ t : ℝ, (windowRatio s t : ℂ) * ((Real.sqrt (h * density ((11/10)*s) t) : ℂ) *
      (Real.sqrt (h * density ((11/10)*s) t) : ℂ)) = ((h * oddWindow s t : ℝ) : ℂ) := by
    intro t
    have hd := density_pos hs' t
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity), ← Complex.ofReal_mul]
    congr 1
    rw [windowRatio, mul_comm h, ← mul_assoc, div_mul_cancel₀ _ hd.ne', mul_comm]
  unfold windowTrace windowDiags heatArray heatWeights weightedArray weight
  refine (h43_tr _ _ _ _ _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have e0 := key (u i - p 0); have e1 := key (u j - p 1); have e2 := key (u k - p 2)
  simp only [show (0:Three)+1 = 1 from rfl, show (1:Three)+1 = 2 from rfl, show (2:Three)+1 = 0 from rfl]
  calc _ = (A 0 i j * A 1 j k * A 2 k i) *
        (((windowRatio s (u i - p 0) : ℂ) * ((Real.sqrt (h * density ((11/10)*s) (u i - p 0)) : ℂ) *
          (Real.sqrt (h * density ((11/10)*s) (u i - p 0)) : ℂ))) *
        ((windowRatio s (u j - p 1) : ℂ) * ((Real.sqrt (h * density ((11/10)*s) (u j - p 1)) : ℂ) *
          (Real.sqrt (h * density ((11/10)*s) (u j - p 1)) : ℂ))) *
        ((windowRatio s (u k - p 2) : ℂ) * ((Real.sqrt (h * density ((11/10)*s) (u k - p 2)) : ℂ) *
          (Real.sqrt (h * density ((11/10)*s) (u k - p 2)) : ℂ)))) := by ring
    _ = _ := by rw [e0, e1, e2]; push_cast; ring

