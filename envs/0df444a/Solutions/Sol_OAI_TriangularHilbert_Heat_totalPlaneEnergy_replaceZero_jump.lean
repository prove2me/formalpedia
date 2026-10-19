-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.totalPlaneEnergy_replaceZero_jump
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:27:26.151746+00:00
-- url     : https://prove2.me/submissions/690de72c-6073-424b-855b-aeb0807d1c1b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/TotalJump.lean:L108-L139
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.totalPlaneEnergy_replaceZero_jump. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Theorems.Thm_OAI_TriangularHilbert_Heat_density_product
import Theorems.Thm_OAI_TriangularHilbert_Heat_density_triple_integrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_heatPlane_integrable
import Theorems.Thm_OAI_TriangularHilbert_Heat_planeIntegral_weight_slice
import Theorems.Thm_OAI_TriangularHilbert_Heat_weight_three_integrable
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_replaceZero_jump_one
import Theorems.Thm_OAI_TriangularHilbert_MatrixEnergy_energy_replaceZero_jump_zero

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

end TriangularHilbert.Heat
end
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.MeshMass ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

lemma integral_density {σ : ℝ} (hσ : 0 < σ) : (∫ t, density σ t) = 1 := by
  rw [density_eq_gaussianPDFReal hσ.le]
  apply ProbabilityTheory.integral_gaussianPDFReal_eq_one
  intro he
  have he' : σ = 0 := congrArg (fun r : NNReal => (r : ℝ)) he
  exact hσ.ne' he'

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianConvolution ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma density_neg (σ x : ℝ) : density σ (-x) = density σ x := by
  simp [density]

lemma integral_density_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    (∫ p, density s (a-p)*density t (b-p)) = density (s+t) (a-b) := by
  simp_rw [density_product hs ht]
  rw [integral_const_mul,integral_sub_right_eq_self,integral_density (by positivity),mul_one]
end
end TriangularHilbert.Heat
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

-- ---- from OAI.Analysis.TriangularHilbert.GaussianTriple ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

lemma integral_density_triple {s t v : ℝ} (hs : 0 < s) (ht : 0 < t) (hv : 0 < v) (a b c : ℝ) :
    (∫ z : ℝ×ℝ, density s (a-z.1)*density t (b-z.2)*density v (c+z.1+z.2)) =
      density (s+t+v) (a+b+c) := by
  rw [MeasureTheory.Measure.volume_eq_prod,integral_prod _ (density_triple_integrable hs ht hv a b c)]
  have inner (p : ℝ) : (∫ q, density s (a-p)*density t (b-q)*density v (c+p+q)) =
      density s (a-p)*density (t+v) (b+c+p) := by
    have he (q : ℝ) : density v (c+p+q) = density v ((-c-p)-q) := by
      rw [show (-c-p)-q = -(c+p+q) by ring,density_neg]
    simp_rw [he,mul_assoc]
    rw [integral_const_mul,integral_density_product ht hv]
    congr 2
    ring
  simp_rw [inner]
  have he (p : ℝ) : density (t+v) (b+c+p) = density (t+v) ((-b-c)-p) := by
    rw [show (-b-c)-p = -(b+c+p) by ring,density_neg]
  simp_rw [he]
  rw [integral_density_product hs (add_pos ht hv)]
  congr 1 <;> ring

lemma planeIntegral_weight_triple (h a b c : ℝ) (σ : MatrixEnergy.Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 2) (σ 2)) 0 =
      h^3*density (σ 0+σ 1+σ 2) (a+b+c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1) * (h*density (σ 1) (b-z.2)) *
      (h*density (σ 2) (c-(0-z.1-z.2)))) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1) * (h*density (σ 1) (b-z.2)) *
      (h*density (σ 2) (c-(0-z.1-z.2))) =
      h^3*(density (σ 0) (a-z.1)*density (σ 1) (b-z.2)*density (σ 2) (c+z.1+z.2)) := by
    rw [show c-(0-z.1-z.2) = c+z.1+z.2 by ring]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_density_triple (hσ 0) (hσ 1) (hσ 2)]
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.ZeroStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_replaceZero_two (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (g : Three → ι → ℝ) :
    rowStar (weightedArray (replaceZero A B) g) 2 = rowStar (weightedArray (replaceZero A C) g) 2 := by
  ext ⟨a,i⟩ ⟨b,j⟩
  simp only [rowStar_apply]
  by_cases ha : a=2
  · subst a
    simp only [ite_true]
    fin_cases b <;> simp [triangleBlocks,weightedArray,replaceZero]
  · simp [ha]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.GaussianExpectation ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
noncomputable section

lemma planeIntegral_weight_repeat_zero (h a b c d : ℝ) (σ : Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 0) (σ 0)) d =
      h^3*density (2*σ 0) (a-c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 0) (c-z.1)) ∂volume.prod volume) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 0) (c-z.1)) =
      h^3*((density (σ 0) (a-z.1)*density (σ 0) (c-z.1))*density (σ 1) (b-z.2)) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun p => density (σ 0) (a-p)*density (σ 0) (c-p)) (fun q => density (σ 1) (b-q)),integral_density_product (hσ 0) (hσ 0),integral_sub_left_eq_self,integral_density (hσ 1),mul_one]
  congr 2
  ring

lemma planeIntegral_weight_repeat_one (h a b c d : ℝ) (σ : Three → ℝ)
    (hσ : ∀ w, 0 < σ w) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h c (p 1) (σ 1)) d =
      h^3*density (2*σ 1) (b-c) := by
  unfold planeIntegral
  change (∫ z : ℝ×ℝ, h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 1) (c-z.2)) ∂volume.prod volume) = _
  have he (z : ℝ×ℝ) : h*density (σ 0) (a-z.1)*(h*density (σ 1) (b-z.2))*(h*density (σ 1) (c-z.2)) =
      h^3*(density (σ 0) (a-z.1)*(density (σ 1) (b-z.2)*density (σ 1) (c-z.2))) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_prod_mul (fun p => density (σ 0) (a-p)) (fun q => density (σ 1) (b-q)*density (σ 1) (c-q)),integral_density_product (hσ 1) (hσ 1),integral_sub_left_eq_self,integral_density (hσ 0),one_mul]
  congr 2
  ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightSlice ----
namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma weight_slice_integrable {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*
      ∑ m, f m*weight h (c m) (chart 2 d z v) (σ v)) := by
  have hi : Integrable (fun z : ℝ×ℝ => ∑ m, f m*(weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h (c m) (chart 2 d z v) (σ v))) :=
    integrable_finsetSum _ (fun m _ => (weight_three_integrable hh a b (c m) d σ hσ v).const_mul (f m))
  convert hi using 1
  ext z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_zero_integral {h : ℝ} (hh : 0 < h) (a b d : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 0) (σ 0)) d = h^2*∑ m, f m*(h*density (2*σ 0) (a-c m)) := by
  rw [planeIntegral_weight_slice hh a b d c f σ hσ 0]
  simp_rw [planeIntegral_weight_repeat_zero h a b _ d σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_one_integral {h : ℝ} (hh : 0 < h) (a b d : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 1) (σ 1)) d = h^2*∑ m, f m*(h*density (2*σ 1) (b-c m)) := by
  rw [planeIntegral_weight_slice hh a b d c f σ hσ 1]
  simp_rw [planeIntegral_weight_repeat_one h a b _ d σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_two_integral {h : ℝ} (hh : 0 < h) (a b : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 2) (σ 2)) 0 = h^2*∑ m, f m*(h*density (σ 0+σ 1+σ 2) (a+b+c m)) := by
  rw [planeIntegral_weight_slice hh a b 0 c f σ hσ 2]
  simp_rw [planeIntegral_weight_triple h a b _ σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.TotalJump ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma sum_energy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    |(∑ v, energy (starGram (weightedArray (replaceZero A B) g) v))-
      (∑ v, energy (starGram (weightedArray (replaceZero A C) g) v))| ≤
      3/2 * ∑ i, ∑ j, ‖B i j-C i j‖*g 0 i*g 1 j*jumpSlicing A g i j := by
  have h0 := energy_replaceZero_jump_zero A B C hB hC g hg
  have h1 := energy_replaceZero_jump_one A B C hB hC g hg
  have h2 : energy (starGram (weightedArray (replaceZero A B) g) 2) =
      energy (starGram (weightedArray (replaceZero A C) g) 2) := by
    simp only [starGram,rowStar_replaceZero_two A B C g]
  rw [Fin.sum_univ_three,Fin.sum_univ_three,h2]
  have he : ∀ a b c d e : ℝ, a+b+c-(d+e+c) = (a-d)+(b-e) := by intros; ring
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add h0 h1).trans_eq _)
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold jumpSlicing
  ring
end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma heat_jumpSlice_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) (i j : ι) :
    Integrable (fun z : ℝ×ℝ => heatWeights h u (chart 2 0 z) σ 0 i*
      heatWeights h u (chart 2 0 z) σ 1 j*jumpSlicing A (heatWeights h u (chart 2 0 z) σ) i j) := by
  have hX := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ 1
  have hY := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ 0
  have hH := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 2 m i‖^2) σ hσ 2
  have hK := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 1 j m‖^2) σ hσ 2
  have hi : Integrable (fun z : ℝ×ℝ =>
    2*(weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 0 i m‖^2*weight h (u m) (chart 2 0 z 1) (σ 1))+
    2*(weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 0 m j‖^2*weight h (u m) (chart 2 0 z 0) (σ 0))+
    (weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 2 m i‖^2*weight h (u m) (chart 2 0 z 2) (σ 2))+
    (weight h (u i) (chart 2 0 z 0) (σ 0)*weight h (u j) (chart 2 0 z 1) (σ 1)*
      ∑ m, ‖A 1 j m‖^2*weight h (u m) (chart 2 0 z 2) (σ 2))) :=
    (((hX.const_mul 2).add (hY.const_mul 2)).add hH).add hK
  convert hi using 1
  ext z
  simp only [heatWeights,jumpSlicing]
  ring

omit [DecidableEq ι] in
lemma planeIntegral_heat_jumpSlice (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) (i j : ι) :
    planeIntegral (fun p => heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*
      jumpSlicing A (heatWeights h u p σ) i j) 0 = h^2*jumpExpectation A h u σ i j := by
  have hX := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ 1
  have hY := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ 0
  have hH := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 2 m i‖^2) σ hσ 2
  have hK := weight_slice_integrable hh (u i) (u j) 0 u (fun m => ‖A 1 j m‖^2) σ hσ 2
  have he (p : Three → ℝ) : heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*
      jumpSlicing A (heatWeights h u p σ) i j =
    2*(weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 0 i m‖^2*weight h (u m) (p 1) (σ 1))+
    2*(weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 0 m j‖^2*weight h (u m) (p 0) (σ 0))+
    (weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 2 m i‖^2*weight h (u m) (p 2) (σ 2))+
    (weight h (u i) (p 0) (σ 0)*weight h (u j) (p 1) (σ 1)*
      ∑ m, ‖A 1 j m‖^2*weight h (u m) (p 2) (σ 2)) := by
    unfold heatWeights jumpSlicing; ring
  simp_rw [he]
  unfold planeIntegral
  erw [integral_add (((hX.const_mul 2).add (hY.const_mul 2)).add hH) hK,
    integral_add ((hX.const_mul 2).add (hY.const_mul 2)) hH,
    integral_add (hX.const_mul 2) (hY.const_mul 2),integral_const_mul,integral_const_mul]
  have hXI := weight_slice_one_integral hh (u i) (u j) 0 u (fun m => ‖A 0 i m‖^2) σ hσ
  have hYI := weight_slice_zero_integral hh (u i) (u j) 0 u (fun m => ‖A 0 m j‖^2) σ hσ
  have hHI := weight_slice_two_integral hh (u i) (u j) u (fun m => ‖A 2 m i‖^2) σ hσ
  have hKI := weight_slice_two_integral hh (u i) (u j) u (fun m => ‖A 1 j m‖^2) σ hσ
  unfold planeIntegral at hXI hYI hHI hKI
  erw [hXI,hYI,hHI,hKI]
  unfold jumpExpectation
  ring

lemma totalPlaneEnergy_replaceZero_jump (A : Three → Matrix ι ι ℂ) (B C : Matrix ι ι ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (hC : ∀ i j, ‖C i j‖ ≤ ‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ v, 0 < σ v) :
    |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤
      3/2*h^2*∑ i, ∑ j, ‖B i j-C i j‖*jumpExpectation A h u σ i j := by
  have hE (M : Three → Matrix ι ι ℂ) : Integrable (fun z : ℝ×ℝ => ∑ v, heatEnergy M h u (chart 2 0 z) σ v) :=
    integrable_finsetSum _ (fun v _ => (heatPlane_integrable M hh u 0 hσ).energy 2 v)
  have hj (i j : ι) : Integrable (fun z : ℝ×ℝ => ‖B i j-C i j‖*(heatWeights h u (chart 2 0 z) σ 0 i*
      heatWeights h u (chart 2 0 z) σ 1 j*jumpSlicing A (heatWeights h u (chart 2 0 z) σ) i j)) :=
    (heat_jumpSlice_integrable A hh u hσ i j).const_mul _
  have hJ := integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hj i j))
  have hb := (abs_integral_le_integral_abs (f := fun z : ℝ×ℝ => (∑ v, heatEnergy (replaceZero A B) h u (chart 2 0 z) σ v)-
      (∑ v, heatEnergy (replaceZero A C) h u (chart 2 0 z) σ v))).trans
    (integral_mono ((hE _).sub (hE _)).abs (hJ.const_mul (3/2)) (fun z => by
      simpa only [heatEnergy,heatArray,mul_assoc] using
        sum_energy_replaceZero_jump A B C hB hC (heatWeights h u (chart 2 0 z) σ)
          (fun v i => (weight_pos hh (hσ v) _ _).le)))
  rw [integral_sub (hE _) (hE _),integral_finsetSum _ (fun v _ => (heatPlane_integrable (replaceZero A B) hh u 0 hσ).energy 2 v),
    integral_finsetSum _ (fun v _ => (heatPlane_integrable (replaceZero A C) hh u 0 hσ).energy 2 v)] at hb
  change |totalPlaneEnergy (replaceZero A B) h u 0 σ-totalPlaneEnergy (replaceZero A C) h u 0 σ| ≤ _ at hb
  apply hb.trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hj i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hj _ j),integral_const_mul]
  change 3/2*(∑ i, ∑ j, ‖B i j-C i j‖*planeIntegral (fun p =>
    heatWeights h u p σ 0 i*heatWeights h u p σ 1 j*jumpSlicing A (heatWeights h u p σ) i j) 0) = _
  simp_rw [planeIntegral_heat_jumpSlice A hh u hσ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.Heat.totalPlaneEnergy_replaceZero_jump.{uι} := @_root_.OAI.TriangularHilbert.Heat.totalPlaneEnergy_replaceZero_jump.{uι}
