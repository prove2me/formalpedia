-- Prove2me | solution 1 for OAI.RuledApproximation.singularField_scaled_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:26:12.455934+00:00
-- url     : https://prove2.me/submissions/4ba85f14-5065-4309-beaf-fd7c4bd36140

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularField.lean:L189-L210
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularField_scaled_hyperbolic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Theorems.Thm_OAI_RuledApproximation_singularField_contDiffAt

-- ---- from OAI.Geometry.RuledCovering.SpecializedCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_charpoly (A : Plane →ₗ[ℝ] Plane) :
    A.charpoly = Polynomial.X ^ 2 -
      Polynomial.C (LinearMap.trace ℝ Plane A) * Polynomial.X + Polynomial.C (LinearMap.det A) := by
  rw [← LinearMap.charpoly_toMatrix A (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.charpoly_fin_two, LinearMap.det_toMatrix,
    ← LinearMap.trace_eq_matrix_trace]

lemma plane_hyperbolic_eigenvalues (A : Plane →ₗ[ℝ] Plane)
    (ht : LinearMap.trace ℝ Plane A = 0) (hd : LinearMap.det A < 0) :
    Module.End.HasEigenvalue A (Real.sqrt (-LinearMap.det A)) ∧
    Module.End.HasEigenvalue A (-Real.sqrt (-LinearMap.det A)) := by
  have hs : Real.sqrt (-LinearMap.det A) ^ 2 = -LinearMap.det A :=
    Real.sq_sqrt (by linarith)
  constructor <;> rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly, ht] <;> simp [hs]

lemma eigenvalue_le_norm (A : Plane →L[ℝ] Plane) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Module.End.HasEigenvalue A.toLinearMap lam) : lam ≤ ‖A‖ := by
  obtain ⟨u, hu⟩ := h.exists_hasEigenvector
  have hue : A u = lam • u := hu.apply_eq_smul
  have hn := A.le_opNorm u
  rw [hue, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hn
  exact le_of_mul_le_mul_right hn (norm_pos_iff.mpr hu.2)

lemma eigenvalue_smul (A : Plane →ₗ[ℝ] Plane) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue A lam) (k : ℝ) :
    Module.End.HasEigenvalue (k • A) (k * lam) := by
  obtain ⟨u, hu⟩ := hlam.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    change k • A u = (k*lam) • u
    rw [hu.apply_eq_smul, mul_smul]
  · exact hu.2

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularField ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma hasFDerivAt_vec2 {f g : Plane → ℝ} {f' g' : Plane →L[ℝ] ℝ} {z : Plane}
    (hf : HasFDerivAt f f' z) (hg : HasFDerivAt g g' z) :
    HasFDerivAt (fun w => vec2 (f w) (g w))
      (f'.smulRight (vec2 1 0) + g'.smulRight (vec2 0 1)) z := by
  have he : (fun w => vec2 (f w) (g w)) =
      (fun w => f w • vec2 1 0 + g w • vec2 0 1) := by
    funext w
    ext i
    fin_cases i <;> simp [vec2]
  rw [he]
  exact (hf.smul_const (vec2 1 0)).add (hg.smul_const (vec2 0 1))

lemma singularField_fderiv (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    fderiv ℝ (singularField p) z =
      matrixCLM ((2-p)*(z 1/(1/2:ℝ))^(p-2)*(z 0/z 1))
        ((z 1/(1/2:ℝ))^(p-2)/2*(p*(p-1)+(2-p)*(p-3)*(z 0/z 1)^2))
        ((z 1/(1/2:ℝ))^(p-2)) ((p-2)*(z 1/(1/2:ℝ))^(p-2)*(z 0/z 1)) := by
  let b : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let r : Plane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hb := b.hasFDerivAt (x := z)
  have hr := r.hasFDerivAt (x := z)
  have hri := (hasDerivAt_inv hz.ne').comp_hasFDerivAt z hr
  have hquot := hb.mul hri
  have hscale := hr.const_mul 2
  have hpow1 := hscale.rpow_const (p := p-1) (Or.inl (by change 2*z 1 ≠ 0; positivity))
  have hpow2 := hscale.rpow_const (p := p-2) (Or.inl (by change 2*z 1 ≠ 0; positivity))
  have hP := (hpow1.const_mul ((1/2:ℝ)/2)).mul
    (((hquot.pow 2).const_mul (2-p)).const_add p)
  have hQ := hpow2.mul hb
  have hf := (hasFDerivAt_vec2 hP hQ).fderiv
  have he : (fun w : Plane => vec2 (((1/2:ℝ)/2)*(2*r w)^(p-1)*
      (p+(2-p)*(b w*(r w)⁻¹)^2)) ((2*r w)^(p-2)*b w)) = singularField p := by
    funext w
    ext i
    fin_cases i <;> simp [singularField,vec2,b,r,div_eq_mul_inv,mul_comm]
  change fderiv ℝ (fun w : Plane => vec2 (((1/2:ℝ)/2)*(2*r w)^(p-1)*
      (p+(2-p)*(b w*(r w)⁻¹)^2)) ((2*r w)^(p-2)*b w)) z = _ at hf
  rw [he] at hf
  rw [hf]
  have h2 : 0 < 2*z 1 := by positivity
  have hp1 : (2*z 1)^(p-1-1) = (2*z 1)^(p-2) := by congr 1; ring
  have hp2 : (2*z 1)^(p-2-1) = (2*z 1)^(p-2)/(2*z 1) := by
    rw [Real.rpow_sub_one h2.ne']
  have hp3 : (2*z 1)^(p-1) = (2*z 1)^(p-2)*(2*z 1) := by
    rw [show p-1 = p-2+1 by ring,Real.rpow_add_one h2.ne']
  ext w i
  fin_cases i <;>
    simp [matrixCLM,b,r,ContinuousLinearMap.smulRight_apply,vec2,hp1,hp2,hp3] <;>
    (rw [show z 1*2=2*z 1 by ring]; field_simp [hz.ne'] <;> ring)

lemma matrixCLM_trace (a b c d : ℝ) :
    LinearMap.trace ℝ Plane (matrixCLM a b c d).toLinearMap = a+d := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.trace_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr,matrixCLM_apply]

lemma matrixCLM_det (a b c d : ℝ) :
    LinearMap.det (matrixCLM a b c d).toLinearMap = a*d-b*c := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr,matrixCLM_apply]

lemma singularField_trace_det (p : ℝ) {z : Plane} (hz : 0 < z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (singularField p) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap =
      ((z 1/(1/2:ℝ))^(p-2))^2*(p-1)/2*((2-p)*(z 0/z 1)^2-p) := by
  rw [singularField_fderiv p hz,matrixCLM_trace,matrixCLM_det]
  constructor <;> ring

lemma singularField_hyperbolic {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1) :
    LinearMap.trace ℝ Plane (fderiv ℝ (singularField p) z).toLinearMap = 0 ∧
    LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap < 0 := by
  obtain ⟨ht,hd⟩ := singularField_trace_det p hz
  refine ⟨ht,?_⟩
  rw [hd]
  have hq : |z 0/z 1| ≤ 1 := by
    rw [abs_div,abs_of_pos hz,div_le_one hz]
    exact hb
  have hq2 : (z 0/z 1)^2 ≤ 1 := by
    have := mul_self_le_mul_self (abs_nonneg (z 0/z 1)) hq
    nlinarith [sq_abs (z 0/z 1)]
  apply mul_neg_of_pos_of_neg
  · exact div_pos (mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos (by positivity) _)) (by linarith)) (by norm_num)
  · have := mul_le_mul_of_nonneg_left hq2 (sub_nonneg.mpr hp2.le)
    nlinarith

lemma singularField_scaled_hyperbolic {p c : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hc : c ≠ 0) {z : Plane} (hz : 0 < z 1) (hb : |z 0| ≤ z 1)
    (hd : |c| *‖fderiv ℝ (singularField p) z‖ < 1) :
    HyperbolicAt 1 (fun w => c • singularField p w) z := by
  have hdiff := (singularField_contDiffAt p hz).differentiableAt (by norm_num)
  rw [HyperbolicAt,fderiv_fun_const_smul hdiff]
  have htd := singularField_hyperbolic hp hp2 hz hb
  have heig := plane_hyperbolic_eigenvalues _ htd.1 htd.2
  let lam := Real.sqrt (-LinearMap.det (fderiv ℝ (singularField p) z).toLinearMap)
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by linarith [htd.2])
  have hnorm : lam ≤ ‖fderiv ℝ (singularField p) z‖ := eigenvalue_le_norm _ hlam.le heig.1
  have hnonneg : 0 < |c| := abs_pos.mpr hc
  refine ⟨|c| *lam,by simpa using mul_pos hnonneg hlam,?_,?_,?_⟩
  · simpa using (mul_le_mul_of_nonneg_left hnorm hnonneg.le).trans_lt hd
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using eigenvalue_smul _ heig.1 c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using eigenvalue_smul _ heig.2 c
  · by_cases hcp : 0 ≤ c
    · simpa [abs_of_nonneg hcp] using eigenvalue_smul _ heig.2 c
    · have hcn : c < 0 := lt_of_not_ge hcp
      simpa [abs_of_neg hcn] using eigenvalue_smul _ heig.1 c

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularField_scaled_hyperbolic := @_root_.OAI.RuledApproximation.singularField_scaled_hyperbolic
