-- Prove2me | solution 2 for OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:23:54.790069+00:00
-- url     : https://prove2.me/submissions/8ae876c1-533e-49a5-b06a-02a69e11e6a1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/InitialAlgebra.lean:L74-L93
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le. The node keeps its source
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
import Theorems.Thm_OAI_TriangularHilbert_weighted_cubic

-- ---- from OAI.Analysis.TriangularHilbert.InitialAlgebra ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma hsSquare_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    hsSquare (weightedArray A g v) = ∑ i, ∑ j, ‖A v i j‖^2 * (g v i*g (v+1) j) := by
  unfold hsSquare weightedArray
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
    Real.sq_sqrt (hg v i),Real.sq_sqrt (hg (v+1) j)]
  ring

lemma hsCube_weightedArray_le (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ v, (∑ i, g v i) ≤ M) (v : Three) :
    hsCube (weightedArray A g v) ≤ M * ∑ i, ∑ j, ‖A v i j‖^3 * (g v i*g (v+1) j) := by
  have hh := TriangularHilbert.weighted_cubic (Finset.univ : Finset (ι×ι))
    (fun a => ‖A v a.1 a.2‖) (fun a => g v a.1*g (v+1) a.2)
    (fun _ _ => norm_nonneg _) (fun a _ => mul_nonneg (hg _ _) (hg _ _))
  simp only [Fintype.sum_prod_type] at hh
  have hw : (∑ i, ∑ j, g v i*g (v+1) j) ≤ M^2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul,pow_two]
    exact mul_le_mul (hm v) (hm (v+1)) (Finset.sum_nonneg (fun j _ => hg _ j)) hM
  have hs : Real.sqrt (∑ i, ∑ j, g v i*g (v+1) j) ≤ M := by
    simpa only [Real.sqrt_sq hM] using Real.sqrt_le_sqrt hw
  unfold hsCube
  rw [hsSquare_weightedArray A g hg]
  exact hh.trans (by
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left hs (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (mul_nonneg (hg _ _) (hg _ _))))))
end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le.{uι}
