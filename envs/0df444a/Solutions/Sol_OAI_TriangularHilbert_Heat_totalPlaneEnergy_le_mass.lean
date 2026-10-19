-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.totalPlaneEnergy_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:25:30.562523+00:00
-- url     : https://prove2.me/submissions/891c784d-e732-4db0-8c04-3ba90d17f94c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/InitialPlane.lean:L27-L55
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.totalPlaneEnergy_le_mass. The node keeps its source
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
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatPlane_integrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_planeIntegral_edgeCubic
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_hsCube_weightedArray_le
import Theorems.Thm_OAI_TriangularHilbert_weighted_cubic

-- ---- from OAI.Analysis.TriangularHilbert.Gaussian ----
namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

theorem density_eq_gaussianPDFReal {σ : ℝ} (hσ : 0 ≤ σ) :
    density σ = ProbabilityTheory.gaussianPDFReal 0 ⟨σ, hσ⟩ := by
  ext t
  change (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t^2 / (2*σ)) =
    (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(t-0)^2 / (2*σ))
  rw [sub_zero]

theorem density_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable (density σ) := by
  rw [density_eq_gaussianPDFReal hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 _

end TriangularHilbert.Heat
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

variable [DecidableEq ι]

theorem traceReal_unitary_conj (U : unitary (Matrix ι ι ℂ)) (X : Matrix ι ι ℂ) :
    traceReal (conjStarAlgAut ℂ _ U X) = traceReal X := by
  unfold traceReal
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem energy_unitary_conj (U : unitary (Matrix ι ι ℂ))
    {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy (conjStarAlgAut ℂ _ U P) = energy P := by
  have hs : CFC.sqrt (conjStarAlgAut ℂ _ U P) =
      conjStarAlgAut ℂ _ U (CFC.sqrt P) := by
    apply CFC.sqrt_unique
    · rw [← map_mul, CFC.sqrt_mul_sqrt_self P hP.nonneg]
    · simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
        ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).mul_mul_conjTranspose_same
          (U : Matrix ι ι ℂ)).nonneg
  simp only [energy, hs, ← map_mul, traceReal_unitary_conj]

theorem sqrt_diagonal_nonneg (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    CFC.sqrt (Matrix.diagonal (fun i => (q i : ℂ))) =
      Matrix.diagonal (fun i => ((Real.sqrt (q i) : ℝ) : ℂ)) := by
  apply CFC.sqrt_unique
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact_mod_cast (Real.mul_self_sqrt (hq i))
  · exact (Matrix.PosSemidef.diagonal (fun i =>
      RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))).nonneg

theorem energy_diagonal (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    energy (Matrix.diagonal (fun i => (q i : ℂ))) = ∑ i, q i * Real.sqrt (q i) := by
  simp [energy, sqrt_diagonal_nonneg q hq, Matrix.diagonal_mul_diagonal, traceReal]

theorem energy_spectral {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P = ∑ i, hP.isHermitian.eigenvalues i * Real.sqrt (hP.isHermitian.eigenvalues i) := by
  rw [← energy_unitary_conj (star hP.isHermitian.eigenvectorUnitary) hP,
    hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  exact energy_diagonal _ hP.eigenvalues_nonneg

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

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

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.PlaneChart ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

lemma chartReflection_preserving (d : ℝ) : MeasurePreserving (chartReflection d) := by
  exact (MeasurePreserving.id volume).skew_product
    (g := fun x y : ℝ => d-x-y) (by fun_prop)
    (Filter.Eventually.of_forall (fun x => (volume.measurePreserving_sub_left (d-x)).map_eq))

lemma swap_preserving : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  ⟨measurable_swap, Measure.prod_swap⟩

lemma chartChange_preserving (i : Three) (d : ℝ) : MeasurePreserving (chartChange i d) := by
  unfold chartChange
  split_ifs
  · exact swap_preserving.comp (chartReflection_preserving d)
  · exact chartReflection_preserving d
  · exact MeasurePreserving.id volume

lemma chartChange_eq (i : Three) (d : ℝ) (z : ℝ × ℝ) :
    chart i d z = chart 2 d (chartChange i d z) := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [chart, chartChange, chartReflection]
  all_goals ring

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MassPlane ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma weight_integrable_center (h u σ : ℝ) (hσ : 0 ≤ σ) :
    Integrable (fun p => weight h u p σ) := by
  exact ((volume.measurePreserving_sub_left u).integrable_comp_of_integrable (density_integrable hσ)).const_mul h

lemma chart_integrable_iff (f : (Three → ℝ) → ℝ) (i j : Three) (d : ℝ) :
    Integrable (fun z : ℝ×ℝ => f (chart i d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart j d z)) := by
  have hi k : Integrable (fun z : ℝ×ℝ => f (chart k d z)) ↔
      Integrable (fun z : ℝ×ℝ => f (chart 2 d z)) := by
    simp_rw [chartChange_eq k d]
    exact (chartChange_preserving k d).integrable_comp_emb (chartChange k d).measurableEmbedding (g := fun z : ℝ×ℝ => f (chart 2 d z))
  exact (hi i).trans (hi j).symm

lemma weight_pair_integrable (h a b d : ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart k d z v) (σ v) *
      weight h b (chart k d z (v+1)) (σ (v+1))) := by
  apply (chart_integrable_iff (fun p => weight h a (p v) (σ v)*weight h b (p (v+1)) (σ (v+1))) (v+2) k d).mp
  change Integrable (fun z : ℝ×ℝ => weight h a (chart (v+2) d z v) (σ v)*weight h b (chart (v+2) d z (v+1)) (σ (v+1))) (volume.prod volume)
  fin_cases v
  · simpa [chart] using (weight_integrable_center h a (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h b (σ 1) (hσ 1).le)
  · simpa [chart] using (weight_integrable_center h a (σ 1) (hσ 1).le).mul_prod
      (weight_integrable_center h b (σ 2) (hσ 2).le)
  · simpa [chart,mul_comm] using (weight_integrable_center h b (σ 0) (hσ 0).le).mul_prod
      (weight_integrable_center h a (σ 2) (hσ 2).le)

variable {ι : Type uι} [Fintype ι]

lemma edgeCubic_integrable (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (d : ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v k : Three) :
    Integrable (fun z : ℝ×ℝ => edgeCubic A h u (chart k d z) σ v) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (weight_pair_integrable h (u i) (u j) d σ hσ v k).const_mul _))

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedCubic ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma energy_le_trace_sqrt {P : Matrix ι ι ℂ} (hP : P.PosSemidef) :
    energy P ≤ traceReal P * Real.sqrt (traceReal P) := by
  have he : traceReal P = ∑ i, hP.isHermitian.eigenvalues i := by
    have hh := congrArg Complex.re hP.isHermitian.trace_eq_sum_eigenvalues
    simp only [Complex.re_sum] at hh
    exact hh
  rw [energy_spectral hP,he,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hP.eigenvalues_nonneg i)
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)

omit [DecidableEq ι] in
lemma traceReal_gram (R : Matrix ι ι ℂ) :
    traceReal (Rᴴ*R) = ∑ i, ∑ j, ‖R i j‖^2 := by
  unfold traceReal Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Finset.sum_comm]

lemma energy_gram_le_HS (R : Matrix ι ι ℂ) :
    energy (Rᴴ*R) ≤ (∑ i, ∑ j, ‖R i j‖^2) * Real.sqrt (∑ i, ∑ j, ‖R i j‖^2) := by
  simpa only [traceReal_gram] using energy_le_trace_sqrt (Matrix.posSemidef_conjTranspose_mul_self R)

end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert
open scoped BigOperators

end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.InitialAlgebra ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma hsSquare_nonneg (R : Matrix ι ι ℂ) : 0 ≤ hsSquare R :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma hsSquare_star (R : Matrix ι ι ℂ) : hsSquare Rᴴ = hsSquare R := by
  unfold hsSquare
  simp only [Matrix.conjTranspose_apply,norm_star]
  rw [Finset.sum_comm]

lemma hsSquare_rowStar_sum [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    hsSquare (rowStar A v) = ∑ w, hsSquare (triangleBlocks A v w) := by
  unfold hsSquare
  simp only [Fintype.sum_prod_type,rowStar_apply]
  have he (a : Three) : (∑ i, ∑ b : Three, ∑ j, ‖if a = v then triangleBlocks A a b i j else 0‖^2) =
      if a = v then (∑ b : Three, ∑ i, ∑ j, ‖triangleBlocks A a b i j‖^2) else 0 := by
    split_ifs with ha
    · exact Finset.sum_comm
    · simp
  simp_rw [he]
  simp

lemma hsSquare_zero : hsSquare (0 : Matrix ι ι ℂ) = 0 := by simp [hsSquare]

lemma hsSquare_rowStar [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    hsSquare (rowStar A v) = hsSquare (A v) + hsSquare (A (v+2)) := by
  rw [hsSquare_rowStar_sum,Fin.sum_univ_three]
  fin_cases v <;> simp [triangleBlocks,hsSquare_zero,hsSquare_star]
  ac_rfl

lemma cubic_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)*Real.sqrt (a+b) ≤ Real.sqrt 2*(a*Real.sqrt a+b*Real.sqrt b) := by
  have hh := TriangularHilbert.weighted_cubic (Finset.univ : Finset (Fin 2))
    ![Real.sqrt a,Real.sqrt b] (fun _ => 1)
    (by intro i _; fin_cases i <;> simp [Real.sqrt_nonneg]) (by simp)
  have he (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x)^3 = x*Real.sqrt x := by
    rw [pow_succ,Real.sq_sqrt hx]
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
    Real.sq_sqrt ha,Real.sq_sqrt hb,he a ha,he b hb,mul_one,one_mul,one_add_one_eq_two,mul_comm] using hh

lemma energy_star_le_hsCube [DecidableEq ι] (A : Three → Matrix ι ι ℂ) (v : Three) :
    energy (starGram A v) ≤ Real.sqrt 2*(hsCube (A v)+hsCube (A (v+2))) := by
  have hh := energy_gram_le_HS (rowStar A v)
  change energy (starGram A v) ≤ hsSquare (rowStar A v)*Real.sqrt (hsSquare (rowStar A v)) at hh
  rw [hsSquare_rowStar] at hh
  exact hh.trans (cubic_add_le (hsSquare_nonneg _) (hsSquare_nonneg _))

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.InitialPlane ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sum_three_shift (f : Three → ℝ) : (∑ v, f (v+2)) = ∑ v, f v := by
  simp [Fin.sum_univ_three]
  ring

lemma totalPlaneEnergy_le_mass (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v)
    {M : ℝ} (hM : 0 ≤ M) (hm : ∀ p v, (∑ i, heatWeights h u p σ v i) ≤ M) :
    totalPlaneEnergy A h u d σ ≤ 2*Real.sqrt 2*M*arrayCubic A h := by
  have hg p v i : 0 ≤ heatWeights h u p σ v i := (weight_pos hh (hσ v) (u i) (p v)).le
  have hb p v : heatEnergy A h u p σ v ≤ Real.sqrt 2*M*(edgeCubic A h u p σ v+edgeCubic A h u p σ (v+2)) := by
    have he := energy_star_le_hsCube (heatArray A h u p σ) v
    have h1 := hsCube_weightedArray_le A (heatWeights h u p σ) (hg p) hM (hm p) v
    have h2 := hsCube_weightedArray_le A (heatWeights h u p σ) (hg p) hM (hm p) (v+2)
    change hsCube (heatArray A h u p σ v) ≤ M*edgeCubic A h u p σ v at h1
    change hsCube (heatArray A h u p σ (v+2)) ≤ M*edgeCubic A h u p σ (v+2) at h2
    exact he.trans (by nlinarith [Real.sqrt_nonneg (2:ℝ)])
  have hi v : planeIntegral (fun p => heatEnergy A h u p σ v) d ≤
      Real.sqrt 2*M*((∑ i, ∑ j, h^2*‖A v i j‖^3)+(∑ i, ∑ j, h^2*‖A (v+2) i j‖^3)) := by
    have ht := integral_mono ((heatPlane_integrable A hh u d hσ).energy 2 v)
      (((edgeCubic_integrable A h u d σ hσ v 2).add
        (edgeCubic_integrable A h u d σ hσ (v+2) 2)).const_mul (Real.sqrt 2*M))
      (fun z => hb (chart 2 d z) v)
    simp only [Pi.add_apply] at ht
    rw [integral_const_mul,integral_add (edgeCubic_integrable A h u d σ hσ v 2)
      (edgeCubic_integrable A h u d σ hσ (v+2) 2)] at ht
    change planeIntegral (fun p => heatEnergy A h u p σ v) d ≤
      Real.sqrt 2*M*(planeIntegral (fun p => edgeCubic A h u p σ v) d+
        planeIntegral (fun p => edgeCubic A h u p σ (v+2)) d) at ht
    simpa only [planeIntegral_edgeCubic A h u d σ hσ] using ht
  have ht := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Three)) => hi v)
  rw [← Finset.mul_sum,Finset.sum_add_distrib,
    sum_three_shift (fun v => ∑ i, ∑ j, h^2*‖A v i j‖^3)] at ht
  exact ht.trans_eq (by unfold arrayCubic; ring)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.totalPlaneEnergy_le_mass.{uι} := @_root_.OAI.TriangularHilbert.Heat.totalPlaneEnergy_le_mass.{uι}
