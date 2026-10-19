-- Prove2me | solution 2 for OAI.TriangularHilbert.Heat.windowTrace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:04:43.030102+00:00
-- url     : https://prove2.me/submissions/d8ac6daf-ae7a-4dc6-97c1-481a4bc9d239

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/SignedExpansion.lean:L49-L71
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.windowTrace_eq. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.GaussianGram ----
namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.TraceWeights ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma trace_mul_three (X Y Z : Matrix ι ι ℂ) :
    Matrix.trace (X*Y*Z) = ∑ i, ∑ j, ∑ k, X i j*Y j k*Z k i := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

lemma trace_diagonal_triangle (W : Three → Matrix ι ι ℂ) (d : Three → ι → ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2) =
      ∑ i, ∑ j, ∑ k, ((d 0 i:ℂ)*W 0 i j)*((d 1 j:ℂ)*W 1 j k)*((d 2 k:ℂ)*W 2 k i) := by
  rw [show Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2 =
      (Matrix.diagonal (fun i => (d 0 i:ℂ))*W 0)*
      (Matrix.diagonal (fun i => (d 1 i:ℂ))*W 1)*
      (Matrix.diagonal (fun i => (d 2 i:ℂ))*W 2) by simp only [Matrix.mul_assoc]]
  simp only [trace_mul_three,Matrix.diagonal_mul]

lemma weighted_triangle_entry (a b c : ℂ) (g0 g1 g2 d0 d1 d2 : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) :
    ((d0:ℂ)*((Real.sqrt g0:ℂ)*a*(Real.sqrt g1:ℂ)))*
    ((d1:ℂ)*((Real.sqrt g1:ℂ)*b*(Real.sqrt g2:ℂ)))*
    ((d2:ℂ)*((Real.sqrt g2:ℂ)*c*(Real.sqrt g0:ℂ))) =
      a*b*c*((g0*d0)*(g1*d1)*(g2*d2):ℝ) := by
  have h0 : (Real.sqrt g0:ℂ)^2 = (g0:ℂ) := by exact_mod_cast Real.sq_sqrt hg0
  have h1 : (Real.sqrt g1:ℂ)^2 = (g1:ℂ) := by exact_mod_cast Real.sq_sqrt hg1
  have h2 : (Real.sqrt g2:ℂ)^2 = (g2:ℂ) := by exact_mod_cast Real.sq_sqrt hg2
  calc
    _ = a*b*c*(Real.sqrt g0:ℂ)^2*(Real.sqrt g1:ℂ)^2*(Real.sqrt g2:ℂ)^2*d0*d1*d2 := by ring
    _ = _ := by rw [h0,h1,h2]; push_cast; ring

lemma trace_weighted_triangle (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) :
    Matrix.trace (Matrix.diagonal (fun i => (d 0 i:ℂ))*weightedArray A g 0*
      Matrix.diagonal (fun i => (d 1 i:ℂ))*weightedArray A g 1*
      Matrix.diagonal (fun i => (d 2 i:ℂ))*weightedArray A g 2) =
      ∑ i, ∑ j, ∑ k, A 0 i j*A 1 j k*A 2 k i*((g 0 i*d 0 i)*(g 1 j*d 1 j)*(g 2 k*d 2 k):ℝ) := by
  rw [trace_diagonal_triangle]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact weighted_triangle_entry _ _ _ _ _ _ _ _ _ (hg 0 i) (hg 1 j) (hg 2 k)

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.SignedExpansion ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section

lemma density_mul_windowRatio {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density ((11/10)*s) t * windowRatio s t = oddWindow s t := by
  unfold windowRatio
  exact mul_div_cancel₀ _ (density_pos (by positivity) _).ne'

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma windowTrace_eq (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) :
    windowTrace A h u p s = ∑ i, ∑ j, ∑ k,
      (h^3:ℝ)* (A 0 i j*A 1 j k*A 2 k i) *
        ((oddWindow s (u i-p 0)*oddWindow s (u j-p 1)*oddWindow s (u k-p 2):ℝ):ℂ) := by
  unfold windowTrace windowDiags heatArray
  have hg (v : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) v i :=
    (weight_pos hh (by positivity) _ _).le
  rw [trace_weighted_triangle A (heatWeights h u p (fun _ => (11/10)*s))
    (fun v i => windowRatio s (u i-p v)) hg]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he (v : Three) (i : ι) : heatWeights h u p (fun _ => (11/10)*s) v i * windowRatio s (u i-p v) =
      h*oddWindow s (u i-p v) := by
    unfold heatWeights weight
    rw [mul_assoc,density_mul_windowRatio hs]
  rw [he,he,he]
  push_cast
  ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.windowTrace_eq.{uι} := @_root_.OAI.TriangularHilbert.Heat.windowTrace_eq.{uι}
