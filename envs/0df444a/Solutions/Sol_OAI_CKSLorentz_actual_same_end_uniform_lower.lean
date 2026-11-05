-- Prove2me | solution 1 for OAI.CKSLorentz.actual_same_end_uniform_lower
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:12:47.875179+00:00
-- url     : https://prove2.me/submissions/5f037573-f405-4005-8840-fbf74d1c3b16

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSMixedGeometry_source_actual_collar_future_regions
import Theorems.Thm_OAI_CKSLorentz_SourceCollarAtlas_eventually_pointwise
import Theorems.Thm_OAI_CKSMixedGeometry_source_collar_metric_comparison
import Theorems.Thm_OAI_CKSLorentz_SourceCollarAtlas_eventually_outer_spatial_lower

set_option linter.all false

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_eq (q : Mat) : inverse q = q⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, ← determinant_eq]
  ext i j
  simp [inverse, div_eq_mul_inv, mul_comm]

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSCalculus
noncomputable section
open Filter Set
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma D_const (e x : E) (c : ℝ) : D e (fun _ => c) x = 0 := by simp [D]
lemma D_add (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y + g y) x = D e f x + D e g x := by
  simp [D, fderiv_fun_add hf hg]
lemma D_sub (e : E) {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f y - g y) x = D e f x - D e g x := by
  simp [D, fderiv_fun_sub hf hg]

lemma D_const_mul (e : E) {f : E → ℝ} {x : E} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) : D e (fun y => c * f y) x = c * D e f x := by
  rw [D_mul e (differentiableAt_const c) hf, D_const]
  ring

lemma contDiffAt_D {f : E → ℝ} {x : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f x)
    {m : ℕ∞ω} (hmn : m + 1 ≤ n) (e : E) : ContDiffAt ℝ m (D e f) x :=
  (hf.fderiv_right hmn).clm_apply contDiffAt_const

lemma D_pow (e : E) {f : E → ℝ} {x : E} (n : ℕ)
    (hf : DifferentiableAt ℝ f x) :
    D e (fun y => f y ^ n) x = n * f x ^ (n - 1) * D e f x := by
  unfold D
  rw [fderiv_fun_pow n hf]
  simp

lemma D_comp_real (e : E) {f : ℝ → ℝ} {g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (g x)) (hg : DifferentiableAt ℝ g x) :
    D e (fun y => f (g y)) x = deriv f (g x) * D e g x := by
  unfold D
  change fderiv ℝ (f ∘ g) x e = _
  rw [(hf.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv]
  simp

end
end CKSCalculus

end









end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma component_diff {n : ℕ∞ω} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (i k : A) : ContDiffAt ℝ n (fun y => q y i k) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_smooth (n : ℝ) : ContDiff ℝ ∞ (radiusPower n) := by unfold radiusPower; fun_prop
lemma radiusPower_diff (n : ℝ) (m : ℕ) (x : Point) : ContDiffAt ℝ m (radiusPower n) x :=
  ((radiusPower_smooth n).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)).contDiffAt

lemma D_radiusPower (n : ℝ) (a : I) :
    D (basis a) (radiusPower n) = fun x => (n*basis a 0)*radiusPower n x := by
  funext x
  have hc : DifferentiableAt ℝ (fun y : Point => y 0) x := by fun_prop
  unfold radiusPower
  rw [D_comp_real (basis a) (Real.differentiableAt_exp) (hc.const_mul n),
    Real.deriv_exp,D_const_mul (basis a) n hc]
  change Real.exp (n*x 0) * (n*D (basis a) (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ) x) = _
  rw [D_clm]
  simp only [ContinuousLinearMap.proj_apply]
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def traceProduct (q p : Mat) : ℝ := ∑ i, ∑ k, q i k*p k i

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma inverse_diff_at {n : ℕ} {q : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ n q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ n (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt.comp x hq
  · exact h0

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t := by
  simp [traceProduct,mul_add,Finset.sum_add_distrib]
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p := by
  simp [traceProduct]
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma metricBlock_submatrix (a : ℝ) (b : Point) (q : Mat) :
    (metricBlock a b q).submatrix Fin.succ Fin.succ = q := by
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

lemma metricBlock_leaf_posDef {a : ℝ} {b : Point} {q : Mat} (h : (metricBlock a b q).PosDef) :
    q.PosDef := by
  have hi : Function.Injective (Fin.succ : I → Fin 3) := Fin.succ_injective 2
  simpa only [metricBlock_submatrix] using h.submatrix hi

lemma inverse_mul_vector (q : Mat) (hq : determinant q ≠ 0) (b : Point) (i : I) :
    ∑ k, q i k*(∑ a, inverse q k a*b a) = b i := by
  fin_cases i <;> simp only [Fin.sum_univ_two,inverse] <;>
    field_simp <;> dsimp [determinant] at * <;> ring

lemma metricBlock_schur_positive {a : ℝ} {b : Point} {q : Mat}
    (h : (metricBlock a b q).PosDef) :
    0 < a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
  have hq : determinant q ≠ 0 := by rw [determinant_eq]; exact (metricBlock_leaf_posDef h).det_pos.ne'
  let s : Point := fun i => ∑ k, inverse q i k*b k
  let v : Fin 3 → ℝ := ![1,-s 0,-s 1]
  have hv : v ≠ 0 := by
    intro hh
    have hh' := congrFun hh 0
    norm_num [v] at hh'
  have hp := h.dotProduct_mulVec_pos hv
  have hquad : (star v) ⬝ᵥ (metricBlock a b q *ᵥ v) = a-∑ i, ∑ k, inverse q i k*(b i*b k) := by
    have hmul0 : q 0 0*s 0+q 0 1*s 1=b 0 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 0
    have hmul1 : q 1 0*s 0+q 1 1*s 1=b 1 := by simpa [s,Fin.sum_univ_two] using inverse_mul_vector q hq b 1
    have hbb : (∑ i, ∑ k, inverse q i k*(b i*b k)) = b 0*s 0+b 1*s 1 := by
      simp [s,Fin.sum_univ_two]
      ring
    rw [hbb]
    simp only [v,metricBlock,Matrix.of_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      star_trivial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      one_mul,neg_mul,mul_neg]
    simp only [Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      mul_one]
    nlinarith [congrArg (fun t : ℝ => t * s 0) hmul0, congrArg (fun t : ℝ => t * s 1) hmul1]
  rwa [hquad] at hp

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_nat (n : ℕ) (x : Point) : radiusPower n x = Real.exp (x 0)^n := by
  exact Real.exp_nat_mul (x 0) n

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

lemma hermitian_real_symmetry {n : Type*} {q : Matrix n n ℝ} (h : q.IsHermitian) (i j : n) :
    q j i=q i j := by
  simpa only [conjTranspose_apply,star_trivial] using congrFun (congrFun h i) j

lemma metricBlock_hermitian (a : ℝ) (b : Point) {q : Mat} (hq : q.IsHermitian) :
    (metricBlock a b q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTranspose_apply,metricBlock,hermitian_real_symmetry hq 0 1]

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse inverse_smul inverse_trace)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radiusPower_neg_nat (n : ℕ) (x : Point) : radiusPower (-(n:ℝ)) x = 1/Real.exp (x 0)^n := by
  rw [radiusPower,neg_mul,Real.exp_neg,Real.exp_nat_mul,one_div]
lemma radiusPower_inverse (x : Point) : radiusPower (-1) x = 1/Real.exp (x 0) := by
  simpa using radiusPower_neg_nat 1 x

lemma radiusPower_two (x : Point) : radiusPower 2 x = Real.exp (x 0)^2 := radiusPower_nat 2 x

lemma traceProduct_add (q p t : Mat) : traceProduct q (p+t) = traceProduct q p+traceProduct q t :=
  CKSAngularGeometry.traceProduct_add q p t
lemma traceProduct_smul (c : ℝ) (q p : Mat) : traceProduct q (c • p) = c*traceProduct q p :=
  CKSAngularGeometry.traceProduct_smul c q p

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

lemma logRadiusChart_smooth : ContDiff ℝ ∞ logRadiusChart := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [logRadiusChart,hi,ite_eq_left]; fun_prop
  · simp only [logRadiusChart,hi,ite_false]; fun_prop

theorem coordinate_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

theorem coordinate_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

def chartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i = 0 then Real.exp (x 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma logRadiusChart_hasFDerivAt (x : Point) : HasFDerivAt logRadiusChart (chartDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [logRadiusChart,chartDerivative,Function.comp_def] using
      (Real.hasDerivAt_exp (x 0)).comp_hasFDerivAt x (ContinuousLinearMap.proj 0 : Point →L[ℝ] ℝ).hasFDerivAt
  · simp only [logRadiusChart,hi,ite_false]
    change HasFDerivAt (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) (ContinuousLinearMap.proj i) x
    exact (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ).hasFDerivAt

lemma chartDerivative_basis (a : I) (x : Point) :
    chartDerivative x (basis a) = radialFactor a (logRadiusChart x) • basis a := by
  ext i
  by_cases ha : a = 0 <;> by_cases hi : i = 0
  · subst a; subst i; simp [chartDerivative,radialFactor,logRadiusChart,basis]
  · subst a; simp [chartDerivative,radialFactor,logRadiusChart,basis,hi]
  · subst i; simp [chartDerivative,radialFactor,basis,ha,Ne.symm ha]
  · simp [chartDerivative,radialFactor,basis,ha,hi]

lemma D_pullback (a : I) {f : Point → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (logRadiusChart x)) :
    D (basis a) (fun y => f (logRadiusChart y)) x = scaledD a f (logRadiusChart x) := by
  unfold D
  change (fderiv ℝ (f ∘ logRadiusChart) x) (basis a) = _
  rw [fderiv_comp x hf (logRadiusChart_hasFDerivAt x).differentiableAt,
    (logRadiusChart_hasFDerivAt x).fderiv]
  simp only [ContinuousLinearMap.comp_apply,chartDerivative_basis,map_smul,smul_eq_mul,scaledD,D]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma foliationMetric_angular (U : ℝ) (γ : Mat) (s : Point) (i j : Fin 2) :
    foliationMetric U γ s i.succ j.succ=γ i j := by
  fin_cases i <;> fin_cases j <;> rfl

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma angularProjection_basis_zero : angularProjection (basis 0) = 0 := by
  ext a
  simp [angularProjection,basis]

lemma D_angularLift {f : Angle → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (angularProjection x)) : D (basis 0) (angularLift f) x = 0 := by
  unfold D angularLift
  change (fderiv ℝ (f ∘ angularProjection) x) (basis 0) = 0
  rw [fderiv_comp x hf angularProjection.differentiableAt,angularProjection.fderiv]
  simp only [ContinuousLinearMap.comp_apply,angularProjection_basis_zero,map_zero]

lemma angularLift_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Angle → E} {x : Point} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f (angularProjection x)) :
    ContDiffAt ℝ n (angularLift f) x := hf.comp x angularProjection.contDiff.contDiffAt

lemma radialMatrixD_angularLift {f : Angle → Mat} {x : Point}
    (hf : ContDiffAt ℝ 1 f (angularProjection x)) : radialMatrixD (angularLift f) x = 0 := by
  funext i k
  exact D_angularLift ((contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k).differentiableAt (by norm_num))

lemma logGammaRadial_actual {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hs : radialMatrixD f.sigma x = 0) (hm : radialMatrixD f.mg x = 0) :
    logGammaRadial f x = (1/Real.exp (x 0)) • radialMatrixD (logGamma f) x := by
  funext i k
  have hσ := (component_diff hf.sigma i k).differentiableAt (by norm_num)
  have hmg := (component_diff hf.mg i k).differentiableAt (by norm_num)
  have heg := (component_diff hf.eg i k).differentiableAt (by norm_num)
  have hp := (radiusPower_diff 2 1 x).differentiableAt (by norm_num)
  have hz := (radiusPower_diff (-1) 1 x).differentiableAt (by norm_num)
  have hfun : (fun y => logGamma f y i k) = fun y =>
      radiusPower 2 y*f.sigma y i k+radiusPower (-1) y*f.mg y i k+f.eg y i k := by
    funext y
    simp [logGamma,radiusPower_two,radiusPower_inverse]
  have hσ0 : D (basis 0) (fun y => f.sigma y i k) x = 0 := congrArg (fun a : Mat => a i k) hs
  have hm0 : D (basis 0) (fun y => f.mg y i k) x = 0 := congrArg (fun a : Mat => a i k) hm
  change (2*Real.exp (x 0))*f.sigma x i k-(1/Real.exp (x 0)^2)*f.mg x i k+
    (1/Real.exp (x 0))*D (basis 0) (fun y => f.eg y i k) x =
      (1/Real.exp (x 0))*D (basis 0) (fun y => logGamma f y i k) x
  erw [hfun,D_add _ ((hp.mul hσ).add (hz.mul hmg)) heg,D_add _ (hp.mul hσ) (hz.mul hmg),
    D_mul _ hp hσ,D_mul _ hz hmg,hσ0,hm0,D_radiusPower,D_radiusPower]
  simp only [basis,Pi.single_eq_same,mul_one,radiusPower_two,radiusPower_inverse]
  have hr := Real.exp_ne_zero (x 0)
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma source_logFields_regular {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) : f.logFields.RegularAt x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  have hmk := hf.mK
  have hmr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hmg hmk hmr
  have hc3 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt (x := x))
  have hc2 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt (x := x))
  exact ⟨angularLift_diff hσ,angularLift_diff hmg,hf.eg.comp x hc3,contDiffAt_const,
    angularLift_diff hmk,hf.ek.comp x hc2,hf.b.comp x hc3,angularLift_diff hmr,hf.err.comp x hc2⟩

lemma source_logGammaRadial_actual {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) :
    logGammaRadial f.logFields x = (1/Real.exp (x 0)) • radialMatrixD (logGamma f.logFields) x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  rw [angularProjection_logRadiusChart] at hσ hmg
  exact logGammaRadial_actual (source_logFields_regular hf)
    (radialMatrixD_angularLift (hσ.of_le (by norm_num)))
    (radialMatrixD_angularLift (hmg.of_le (by norm_num)))

lemma sourceGamma_pullback (f : SourceMassFields) :
    (fun y => sourceGamma f (logRadiusChart y)) = logGamma f.logFields := by
  funext y
  simp [sourceGamma,logGamma,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceTangentialK_pullback (f : SourceMassFields) :
    (fun y => sourceTangentialK f (logRadiusChart y)) = logTangentialK f.logFields := by
  funext y
  simp [sourceTangentialK,logTangentialK,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceRadialMetric_pullback (f : SourceMassFields) :
    (fun y => sourceRadialMetric f (logRadiusChart y)) = logRadialMetric f.logFields := by
  funext y
  simp [sourceRadialMetric,logRadialMetric,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma lapse_radical_reconstruction {r T F : ℝ} (hr : 0 < r) :
    1+(r*(1+(1/r)^3*T))^2-2*F/r =
      (1+r^2)*(1+(1/r)^3*((2*T+(1/r)^3*T^2-2*F)/(1+(1/r)^2))) := by
  have hz : 1+(1/r)^2 ≠ 0 := by positivity
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma sourceGamma_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ 3 (sourceGamma f) y := by
  have hr : ContDiffAt ℝ 3 (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

def sourceGammaRadial (f : SourceMassFields) : Point → Mat := radialMatrixD (sourceGamma f)

def sourceExpansion (f : SourceMassFields) : Point → ℝ := fun y =>
  (y 0)/4*traceProduct (inverse (sourceGamma f y))
    (sourceGammaRadial f y-(show Mat from normalizedLie (sourceGamma f) (sourceShift f) y))

def sourcePhysicalMass (f : SourceMassFields) : Point → ℝ := fun y =>
  (y 0)/2*(1+((y 0)/2*traceProduct (inverse (sourceGamma f y)) (sourceTangentialK f y))^2-
    ((1/Real.sqrt (sourceSchur f y))*sourceExpansion f y)^2)

lemma sourceShift_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (h0 : determinant (sourceGamma f y) ≠ 0) : ContDiffAt ℝ 3 (sourceShift f) y := by
  have hi := inverse_diff_at (sourceGamma_regular hf hy) h0
  apply contDiffAt_pi.mpr
  intro a
  exact ContDiffAt.sum fun b _ => (component_diff hi a b).mul (contDiffAt_pi.mp hf.b b)

lemma sourceShift_pullback (f : SourceMassFields) :
    (fun y => sourceShift f (logRadiusChart y)) = logShift f.logFields := by
  funext x a
  unfold sourceShift logShift
  have hq := congrFun (sourceGamma_pullback f) x
  rw [hq]
  rfl

lemma sourceSchur_pullback (f : SourceMassFields) :
    (fun y => sourceSchur f (logRadiusChart y)) = logSchur f.logFields := by
  funext x
  unfold sourceSchur logSchur
  have hq := congrFun (sourceGamma_pullback f) x
  have hr := congrFun (sourceRadialMetric_pullback f) x
  rw [hq,hr]
  rfl

lemma normalizedLie_pullback {q : Point → Mat} {S : Point → Angle} {x : Point}
    (hq : ContDiffAt ℝ 1 q (logRadiusChart x)) (hS : ContDiffAt ℝ 1 S (logRadiusChart x)) (i k : A) :
    normalizedLie (fun y => q (logRadiusChart y)) (fun y => S (logRadiusChart y)) x i k =
      normalizedLie q S (logRadiusChart x) i k := by
  unfold normalizedLie
  apply Finset.sum_congr rfl
  intro a _
  have hqd (i k : A) := (component_diff hq i k).differentiableAt (by norm_num)
  have hSd (i : A) := (contDiffAt_pi.mp hS i).differentiableAt (by norm_num)
  erw [D_pullback a.succ (hqd i k),D_pullback i.succ (hSd a),D_pullback k.succ (hSd a)]
  simp [scaledD,radialFactor]

lemma sourceGammaRadial_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) :
    sourceGammaRadial f (logRadiusChart x) = logGammaRadial f.logFields x := by
  rw [source_logGammaRadial_actual hf,← sourceGamma_pullback]
  funext i k
  change D (basis 0) (fun y => sourceGamma f y i k) (logRadiusChart x) =
    (1/Real.exp (x 0))*D (basis 0) (fun y => sourceGamma f (logRadiusChart y) i k) x
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hd := (component_diff (sourceGamma_regular hf hr) i k).differentiableAt (by norm_num)
  erw [D_pullback 0 hd]
  simp [scaledD,radialFactor,logRadiusChart]

lemma sourceExpansion_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0) :
    sourceExpansion f (logRadiusChart x) = logExpansion f.logFields x := by
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hq := sourceGamma_regular hf hr
  have hS := sourceShift_regular hf hr h0
  have hLie : (show Mat from normalizedLie (sourceGamma f) (sourceShift f) (logRadiusChart x)) =
      (show Mat from normalizedLie (logGamma f.logFields) (logShift f.logFields) x) := by
    funext i k
    rw [← sourceGamma_pullback,← sourceShift_pullback]
    exact (normalizedLie_pullback (hq.of_le (by norm_num)) (hS.of_le (by norm_num)) i k).symm
  unfold sourceExpansion logExpansion
  rw [sourceGammaRadial_pullback hf,hLie]
  have hγ := congrFun (sourceGamma_pullback f) x
  rw [hγ]
  rfl

lemma sourcePhysicalMass_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (hp : (sourceMetric f (logRadiusChart x)).PosDef) :
    sourcePhysicalMass f (logRadiusChart x) = logPhysicalMass f.logFields x := by
  have h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  unfold sourcePhysicalMass logPhysicalMass
  rw [sourceExpansion_pullback hf h0]
  have hγ := congrFun (sourceGamma_pullback f) x
  have hk := congrFun (sourceTangentialK_pullback f) x
  have hs := congrFun (sourceSchur_pullback f) x
  rw [hγ,hk,hs]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceAspect (f : SourceMassFields) (w : Angle) : ℝ :=
  traceProduct (inverse (f.sigma w)) (f.mg w+(2:ℝ) • f.mK w)+2*f.mr w

lemma source_leading_mass (f : SourceMassFields) : cksLeadingField f.logFields =
    fun y => sourceAspect f (angularProjection y)/4 := by
  funext y
  unfold cksLeadingField SourceMassFields.logFields angularLift sourceAspect
  rw [traceProduct_add,traceProduct_smul]
  ring

lemma SourceMassFields.RegularAt.eventually {f : SourceMassFields} {x : Point} (hf : f.RegularAt x) :
    ∀ᶠ y in 𝓝 x, f.RegularAt y := by
  have hc := angularProjection.continuous.continuousAt (x := x)
  filter_upwards [hc.tendsto.eventually (hf.sigma.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mg.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mK.eventually (by norm_num)),
    hc.tendsto.eventually (hf.mr.eventually (by norm_num)),
    hf.eg.eventually (by norm_num),hf.ek.eventually (by norm_num),
    hf.b.eventually (by norm_num),hf.err.eventually (by norm_num)]
    with y hs hm hk hmr he hek hb herr
  exact ⟨hs,hm,hk,hmr,he,hek,hb,herr⟩

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma injection_basis (a : A) : injection (CKSAngularGeometry.basis a)=CKSMixedGeometry.basis a.succ := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [CKSMixedGeometry.basis]
  · simp [CKSAngularGeometry.basis,CKSMixedGeometry.basis,Pi.single_apply]

lemma slice_hasFDerivAt (r : ℝ) (x : AP) : HasFDerivAt (slice r) injection x :=
  injection.hasFDerivAt.const_add _
lemma slice_smooth (r : ℝ) : ContDiff ℝ ∞ (slice r) :=
  contDiff_const.add injection.contDiff

lemma D_slice (a : A) (r : ℝ) {f : MP → ℝ} {x : AP}
    (hf : DifferentiableAt ℝ f (slice r x)) :
    D (CKSAngularGeometry.basis a) (fun y => f (slice r y)) x=
      D (CKSMixedGeometry.basis a.succ) f (slice r x) := by
  unfold D
  erw [fderiv_comp x hf (slice_hasFDerivAt r x).differentiableAt,
    (slice_hasFDerivAt r x).fderiv,ContinuousLinearMap.comp_apply,injection_basis]

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceT (f : SourceMassFields) : Point → ℝ := fun y =>
  (1/2:ℝ)*traceProduct (inverse (sourceGamma f y)) (sourceTangentialK f y)

lemma sourceT_pullback (f : SourceMassFields) :
    (fun y => sourceT f (logRadiusChart y)) = logT f.logFields := by
  funext y
  unfold sourceT logT
  rw [congrFun (sourceGamma_pullback f) y,congrFun (sourceTangentialK_pullback f) y]

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure LogCollarData.RegularAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma x
  metricError : ContDiffAt ℝ 3 f.metricError x
  shift : ContDiffAt ℝ 3 f.shift x
  tError : ContDiffAt ℝ 2 f.tError x
  LError : ContDiffAt ℝ 2 f.LError x
  massError : ContDiffAt ℝ 2 f.massError x
  fstar : ContDiffAt ℝ 2 f.fstar x
  etaDivR : ContDiffAt ℝ 2 f.etaDivR x
  tauDivR2 : ContDiffAt ℝ 2 f.tauDivR2 x

end
end CKSAngularSlice

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceOriginalL (f : SourceTensorFields) : Point → ℝ := fun y =>
  (1/Real.sqrt (sourceSchur f.base y))^2*(sourceRadialK f y-
    2*∑ a, sourceShift f.base y a*f.kb y a+
    ∑ a, ∑ b, sourceTangentialK f.base y a b*(sourceShift f.base y a*sourceShift f.base y b))

def sourceOriginalEta (f : SourceTensorFields) : Point → A → ℝ := fun y a =>
  (1/Real.sqrt (sourceSchur f.base y))*(f.kb y a-∑ b, sourceShift f.base y b*sourceTangentialK f.base y b a)

def sourceOriginalTau (f : SourceTensorFields) : Point → Mat := fun y =>
  sourceTangentialK f.base y-
    (traceProduct (inverse (sourceGamma f.base y)) (sourceTangentialK f.base y)/2) • sourceGamma f.base y

lemma sourceOriginalL_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalL f (logRadiusChart y)) = logOriginalL f.logFields := by
  funext y
  unfold sourceOriginalL logOriginalL
  have hs := congrFun (sourceSchur_pullback f.base) y
  have hshift := congrFun (sourceShift_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hs,hshift,hk]
  rfl

lemma sourceOriginalEta_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalEta f (logRadiusChart y)) = logOriginalEta f.logFields := by
  funext y a
  unfold sourceOriginalEta logOriginalEta
  have hs := congrFun (sourceSchur_pullback f.base) y
  have hshift := congrFun (sourceShift_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hs,hshift,hk]
  rfl

lemma sourceOriginalTau_pullback (f : SourceTensorFields) :
    (fun y => sourceOriginalTau f (logRadiusChart y)) = logOriginalTau f.logFields := by
  funext y
  unfold sourceOriginalTau logOriginalTau
  have hq := congrFun (sourceGamma_pullback f.base) y
  have hk := congrFun (sourceTangentialK_pullback f.base) y
  rw [hq,hk]
  rfl

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI



noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logQError_scaled (f : MassFields) (x : Point) :
    logQError f x=(1/Real.exp (x 0)^2) • logGamma f x-f.sigma x := by
  funext a b
  simp only [logQError,logGamma,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [show (-3:ℝ)=-(3:ℕ) by norm_num,show (-2:ℝ)=-(2:ℕ) by norm_num,
    radiusPower_neg_nat,radiusPower_neg_nat]
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma roundingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (roundingWeight R) := by
  unfold roundingWeight
  fun_prop

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open CKSMixedGeometry (basis radiusPower)
open CKSBending
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radialLift_diff {h : ℝ → ℝ} {y : MP} (hh : DifferentiableAt ℝ h (Real.exp (y 0))) :
    DifferentiableAt ℝ (radialLift h) y := hh.comp y (by fun_prop)

lemma radialLift_D {h : ℝ → ℝ} {y : MP} (hh : DifferentiableAt ℝ h (Real.exp (y 0))) :
    D (basis 0) (radialLift h) y=Real.exp (y 0)*deriv h (Real.exp (y 0)) := by
  unfold radialLift
  rw [D_comp_real (g := fun y : MP => Real.exp (y 0)) _ hh (by fun_prop)]
  have he : (fun y : MP => Real.exp (y 0))=radiusPower 1 := by
    funext y; simp [radiusPower]
  rw [he,CKSMixedGeometry.D_radiusPower]
  simp [basis,radiusPower]
  ring

lemma collarQ_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    collarQ R f (slice ρ x)=CKSAngularGeometry.fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a b
  simp [collarQ,radialLift,CKSAngularGeometry.fieldQ,collarParams,LogCollarData.angular]
  field_simp

lemma collarShift_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^5 • collarShift R f (slice ρ x)=
      CKSAngularGeometry.fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a
  simp [collarShift,radialLift,CKSAngularGeometry.fieldS,collarParams,LogCollarData.angular]
  ring

lemma collarT_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3*(collarT R f (slice ρ x)-1)=
      CKSAngularGeometry.fieldT (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarT,radialLift,CKSAngularGeometry.fieldT,collarParams,LogCollarData.angular]
  ring

lemma collarF_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    collarF R f (slice ρ x)=CKSAngularGeometry.fieldF (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarF,radialLift,CKSAngularGeometry.fieldF,collarParams,LogCollarData.angular]
  ring

lemma collarQ_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x))
    (hσ : ∀ a b, D (basis 0) (fun y => f.sigma y a b) (slice ρ x)=0) (a b : Fin 2) :
    Real.exp ρ^3*D (basis 0) (fun y => collarQ R f y a b) (slice ρ x)=
      CKSAngularGeometry.fieldQr (collarParams R (Real.exp ρ)) (f.angular ρ) x a b := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have hs := (CKSMixedGeometry.component_diff hf.sigma a b).differentiableAt (by norm_num)
  have hm := (CKSMixedGeometry.component_diff hf.metricError a b).differentiableAt (by norm_num)
  change Real.exp ρ^3*D (basis 0) (fun y => f.sigma y a b+
    (1-radialLift (roundingWeight R) y)*f.metricError y a b) (slice ρ x)=_
  erw [D_add _ hs (((differentiableAt_const (1:ℝ)).sub he).mul hm),D_mul _ ((differentiableAt_const (1:ℝ)).sub he) hm,
    D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,hσ,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  change _ = (1-roundingWeight R (Real.exp ρ))*(Real.exp ρ^3*
    D (basis 0) (fun y => f.metricError y a b) (slice ρ x))-
      (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(Real.exp ρ^3*f.metricError (slice ρ x) a b)
  dsimp only [Pi.sub_apply,radialLift]
  simp only [slice_zero]
  ring

end
end CKSAngularSlice

end


end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radialNormalize_foliation {r U : ℝ} (hr : 0<r) (hU : U ≠ 0) (q : Mat) (S : Point) :
    radialNormalize r (foliationMetric (Real.sqrt (1+r^2)*U) (r^2 • q) ((1/r)^5 • S))=
      normalizedFoliationMetric (1/r) U q S := by
  have hr0 := hr.ne'
  have hi : 1+r^2 = r^2*(1+(1/r)^2) := by field_simp; ring
  have hs : Real.sqrt (1+r^2)=r*Real.sqrt (1+(1/r)^2) := by
    conv_lhs => rw [hi,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
  have hs0 : Real.sqrt (1+(1/r)^2) ≠ 0 := by positivity
  have hsq : Real.sqrt (1+(1/r)^2)^2=1+(1/r)^2 := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialNormalize,radialScale,foliationMetric,normalizedFoliationMetric,
      metricBlock,Matrix.of_apply,Fin.sum_univ_two,hs]
  all_goals field_simp
  all_goals try rw [Real.sq_sqrt (show 0 ≤ (r^2+1)/r^2 by positivity)]
  all_goals field_simp

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

lemma quadratic3_radialNormalize (r : ℝ) (g : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 (radialNormalize r g) v=quadratic3 g (fun i => radialScale r i*v i) := by
  unfold quadratic3 radialNormalize
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma radialScale_ne_zero {r : ℝ} (hr : r ≠ 0) (i : Fin 3) : radialScale r i ≠ 0 := by
  fin_cases i
  · change Real.sqrt (1+r^2) ≠ 0
    positivity
  · change 1/r ≠ 0
    exact one_div_ne_zero hr
  · change 1/r ≠ 0
    exact one_div_ne_zero hr

lemma radialNormalize_comparison {r c : ℝ} {G g : AmbientMat} (hr : r ≠ 0)
    (h : ∀ v, c*quadratic3 (radialNormalize r g) v ≤ quadratic3 (radialNormalize r G) v) :
    ∀ v, c*quadratic3 g v ≤ quadratic3 G v := by
  intro v
  have hh := h (fun i => v i/radialScale r i)
  rw [quadratic3_radialNormalize,quadratic3_radialNormalize] at hh
  have he : (fun i => radialScale r i*(v i/radialScale r i))=v := by
    funext i
    field_simp [radialScale_ne_zero hr i]
  rwa [he] at hh

end
end CKSAngularGeometry

end

end OAI
end

section
namespace OAI




noncomputable section
namespace CKSLorentz
noncomputable section
open scoped RealInnerProductSpace ContDiff

def hyperbolicMetric (x Y Z : E) : ℝ :=
  inner ℝ Y Z - inner ℝ x Y * inner ℝ x Z / (1+‖x‖^2)

end
end CKSLorentz

end




noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Set Filter CKSCalculus
open scoped Topology ContDiff

lemma sum_coordinate_basis (v : Point) : ∑ k : I, v k • basis k = v := by
  ext k
  simp [basis, Finset.sum_apply, Pi.single_apply]

end
end CKSMixedGeometry

end






































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

lemma angularProjection_slice (r : ℝ) (θ : Angle) : angularProjection (slice r θ)=θ := by
  ext a
  exact slice_succ r θ a

end
end CKSLorentz

end






noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set
open scoped ContDiff Topology

attribute [local instance] stereoDimension

namespace SmoothAngularPatch

lemma sphereRegion_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (P.sphereRegion W) :=
  P.chart.isOpen_inter_preimage hW

lemma param_chart (P : SmoothAngularPatch) {n : Sphere} (hn : n ∈ P.chart.source) :
    P.param (P.chart n)=(n:E) := congrArg Subtype.val (P.chart.left_inv hn)

end SmoothAngularPatch
end
end CKSLorentz

end










noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped ContDiff Topology

namespace SmoothAngularPatch

lemma param_fderiv_leftInverse (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) :
    (fderiv ℝ P.extension (P.param θ)).comp (fderiv ℝ P.param θ) =
      ContinuousLinearMap.id ℝ Angle := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hψ := (P.extension_contDiffAt_param hθ).differentiableAt (by simp)
  have hg : (fun η => P.extension (P.param η)) =ᶠ[𝓝 θ] id := by
    filter_upwards [P.chart.open_target.mem_nhds hθ] with η hη
    exact P.extension_param hη
  have ht := hg.fderiv_eq (𝕜:=ℝ)
  change fderiv ℝ (P.extension ∘ P.param) θ = fderiv ℝ id θ at ht
  rw [fderiv_comp θ hψ hφ,fderiv_id] at ht
  exact ht

lemma param_fderiv_injective (P : SmoothAngularPatch) {θ : Angle}
    (hθ : θ ∈ P.chart.target) : Function.Injective (fderiv ℝ P.param θ) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ P.extension (P.param θ)) hvw
  have hl := P.param_fderiv_leftInverse hθ
  have hv := congrArg (fun L : Angle →L[ℝ] Angle => L v) hl
  have hw := congrArg (fun L : Angle →L[ℝ] Angle => L w) hl
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
    hv.symm.trans (h.trans hw)

lemma param_tangent (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target)
    (v : Angle) : inner ℝ (P.param θ) (fderiv ℝ P.param θ v) = 0 := by
  have hφ := (P.param_contDiffAt hθ).differentiableAt (by simp)
  have hconst : (fun η => inner ℝ (P.param η) (P.param η)) = fun _ : Angle => (1:ℝ) := by
    funext η
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖P.param η‖=1 := P.param_norm η
    rw [hn,one_pow]
  have hd := fderiv_inner_apply (𝕜:=ℝ) hφ hφ v
  rw [hconst] at hd
  simp only [fderiv_fun_const] at hd
  change 0 = inner ℝ (P.param θ) (fderiv ℝ P.param θ v) +
    inner ℝ (fderiv ℝ P.param θ v) (P.param θ) at hd
  have hc := real_inner_comm (fderiv ℝ P.param θ v) (P.param θ)
  linarith

lemma roundMetric_posDef (P : SmoothAngularPatch) {θ : Angle} (hθ : θ ∈ P.chart.target) :
    (angularRoundMetric P.param θ).PosDef := by
  change (Matrix.gram ℝ (fun a => fderiv ℝ P.param θ (CKSAngularGeometry.basis a))).PosDef
  apply Matrix.posDef_gram_iff_linearIndependent.mpr
  have h := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map'
    (fderiv ℝ P.param θ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (P.param_fderiv_injective hθ))
  simpa only [Function.comp_def,Pi.basisFun_apply,CKSAngularGeometry.basis,
    ContinuousLinearMap.coe_coe] using h

end SmoothAngularPatch

lemma angular_vector_expansion (v : Angle) :
    ∑ a : Fin 2, v a • CKSAngularGeometry.basis a = v := by
  funext i
  fin_cases i <;> simp [CKSAngularGeometry.basis,Pi.single_apply]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus Set Filter
open scoped Topology ContDiff

lemma fderiv_coordinate_expansion {F : Point → Point} {y : Point}
    (hF : DifferentiableAt ℝ F y) (a : I) :
    fderiv ℝ F y (basis a) = ∑ i, D (basis a) (fun z => F z i) y • basis i := by
  conv_lhs => rw [← sum_coordinate_basis (fderiv ℝ F y (basis a))]
  congr 1; funext i
  congr 1
  simp only [D,fderiv_apply hF,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
lemma coordinateTensorPullback_polar {F : Point → Point} {y : Point}
    (hF : DifferentiableAt ℝ F y) (Q : SmoothAngularPatch) (A : SpatialTensor) (a b : I) :
    coordinateTensorPullback F (polarTensorComponents Q A) a b y =
      A (polarParam Q (F y))
        (fderiv ℝ (polarParam Q) (F y) (fderiv ℝ F y (basis a)))
        (fderiv ℝ (polarParam Q) (F y) (fderiv ℝ F y (basis b))) := by
  rw [fderiv_coordinate_expansion hF a,fderiv_coordinate_expansion hF b]
  simp only [map_sum,map_smul,_root_.sum_apply,smul_apply,
    smul_eq_mul,Finset.mul_sum,coordinateTensorPullback,polarTensorComponents]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma polarTensor_covariance {F : Point → Point} {H : E → E} {y : Point}
    (P Q : SmoothAngularPatch) (A : SpatialTensor)
    (hF : DifferentiableAt ℝ F y)
    (hP : DifferentiableAt ℝ (polarParam P) y)
    (hQ : DifferentiableAt ℝ (polarParam Q) (F y))
    (hH : DifferentiableAt ℝ H (polarParam P y))
    (he : (polarParam Q ∘ F) =ᶠ[𝓝 y] (H ∘ polarParam P)) (a b : I) :
    coordinateTensorPullback F (polarTensorComponents Q A) a b y =
      polarTensorComponents P (spatialTensorPullback H A) a b y := by
  have hp : polarParam Q (F y)=H (polarParam P y) := he.eq_of_nhds
  have hd := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp y hQ hF,fderiv_comp y hH hP] at hd
  have ha := congrArg (fun L : Point →L[ℝ] E => L (basis a)) hd
  have hb := congrArg (fun L : Point →L[ℝ] E => L (basis b)) hd
  simp only [ContinuousLinearMap.comp_apply] at ha hb
  rw [coordinateTensorPullback_polar hF Q A a b,hp,ha,hb]
  rfl
end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma angularRadialTail_open (R : ℝ) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (angularRadialTail R W) := by
  exact (isOpen_Ioi.preimage (continuous_apply 0)).inter
    (hW.preimage angularProjection.continuous)

end
end CKSLorentz

end









noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry
open CKSAngularGeometry (metricBlock AmbientMat)

def cksReference (σ : Angle → Mat) (y : Point) : AmbientMat :=
  metricBlock (1/(1+(y 0)^2)) 0 ((y 0)^2 • σ (angularProjection y))
end
end CKSLorentz

end











noncomputable section
namespace CKSTensorNaturality
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
abbrev Bilinear (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E →L[ℝ] ℝ
def tensorPullback (f : E → F) (T : F → Bilinear F) (x : E) : Bilinear E :=
  (T (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)

def tensorLie (T : E → Bilinear E) (V : E → E) (x v w : E) : ℝ :=
  (fderiv ℝ T x (V x)) v w + T x (fderiv ℝ V x v) w + T x v (fderiv ℝ V x w)
end
end CKSTensorNaturality

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma differentiableAt_flip {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {B : E → F →L[ℝ] G →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) : DifferentiableAt ℝ (fun y => (B y).flip) x := by
  have hf : DifferentiableAt ℝ (fun b : F →L[ℝ] G →L[ℝ] ℝ => b.flip) (B x) :=
    (ContinuousLinearMap.flipₗᵢ ℝ F G ℝ).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt
  exact DifferentiableAt.comp (𝕜 := ℝ) (F := F →L[ℝ] G →L[ℝ] ℝ)
    (G := G →L[ℝ] F →L[ℝ] ℝ) x hf hB
lemma differentiableAt_bilinearComp {B : E → Bilinear F} {A : E → E →L[ℝ] F} {x : E}
    (hB : DifferentiableAt ℝ B x) (hA : DifferentiableAt ℝ A x) :
    DifferentiableAt ℝ (fun y => (B y).bilinearComp (A y) (A y)) x := by
  exact differentiableAt_flip ((differentiableAt_flip (hB.clm_comp hA)).clm_comp hA)
lemma fderiv_bilinear_apply {B : E → Bilinear F} {u v : E → F} {x : E}
    (hB : DifferentiableAt ℝ B x) (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (a : E) :
    fderiv ℝ (fun y => B y (u y) (v y)) x a =
      B x (fderiv ℝ u x a) (v x) + B x (u x) (fderiv ℝ v x a) +
        (fderiv ℝ B x a) (u x) (v x) := by
  rw [fderiv_clm_apply (hB.clm_apply hu) hv, fderiv_clm_apply hB hu]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring
lemma fderiv_bilinear_const {B : E → Bilinear F} {x : E}
    (hB : DifferentiableAt ℝ B x) (v w : F) (a : E) :
    fderiv ℝ (fun y => B y v w) x a = (fderiv ℝ B x a) v w := by
  simpa using fderiv_bilinear_apply hB
    (differentiableAt_const (c := v)) (differentiableAt_const (c := w)) a
lemma differentiableAt_tensorPullback {f : E → F} {T : F → Bilinear F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hT : DifferentiableAt ℝ T (f x)) :
    DifferentiableAt ℝ (tensorPullback f T) x := by
  exact differentiableAt_bilinearComp (hT.comp (G := Bilinear F) x (hf.differentiableAt (by norm_num)))
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
end
end CKSTensorNaturality

end

noncomputable section
namespace CKSTensorNaturality
noncomputable section
open Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [completeF : CompleteSpace F]
omit completeF in
lemma fderiv_tensorPullback [CompleteSpace F] {f : E → F} {T : F → Bilinear F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hT : DifferentiableAt ℝ T (f x)) (a v w : E) :
    (fderiv ℝ (tensorPullback f T) x a) v w =
      T (f x) (fderiv ℝ (fderiv ℝ f) x a v) (fderiv ℝ f x w) +
      T (f x) (fderiv ℝ f x v) (fderiv ℝ (fderiv ℝ f) x a w) +
      (fderiv ℝ T (f x) (fderiv ℝ f x a)) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hTf : DifferentiableAt ℝ (fun y => T (f y)) x := hT.comp (G := Bilinear F) x hfd
  rw [← fderiv_bilinear_const (differentiableAt_tensorPullback hf hT) v w a]
  change fderiv ℝ (fun y => T (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) x a = _
  rw [fderiv_bilinear_apply hTf (hA.clm_apply (differentiableAt_const v))
    (hA.clm_apply (differentiableAt_const w))]
  rw [fderiv_clm_apply hA (differentiableAt_const v),
    fderiv_clm_apply hA (differentiableAt_const w)]
  rw [show fderiv ℝ (fun y => T (f y)) x =
    (fderiv ℝ T (f x)).comp (fderiv ℝ f x) from fderiv_fun_comp (G := Bilinear F) x hT hfd]
  simp

theorem tensorLie_natural {f : E → F} {T : F → Bilinear F}
    {V : F → F} {W : E → E} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hT : DifferentiableAt ℝ T (f x))
    (hV : DifferentiableAt ℝ V (f x)) (hW : DifferentiableAt ℝ W x)
    (hrel : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (W y) = V (f y)) (v w : E) :
    tensorLie (tensorPullback f T) W x v w =
      tensorLie T V (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := hf.isSymmSndFDerivAt (by simp)
  have hD (u : E) : fderiv ℝ f x (fderiv ℝ W x u) +
      fderiv ℝ (fderiv ℝ f) x (W x) u =
        fderiv ℝ V (f x) (fderiv ℝ f x u) := by
    have h := congrArg (fun A : E →L[ℝ] F => A u) (Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hrel)
    rw [fderiv_clm_apply hA hW] at h
    rw [show fderiv ℝ (fun y => V (f y)) x =
      (fderiv ℝ V (f x)).comp (fderiv ℝ f x) from fderiv_comp x hV hfd] at h
    simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      hsymm u (W x)] using h
  unfold tensorLie
  rw [fderiv_tensorPullback hf hT, hrel.self_of_nhds]
  simp only [tensorPullback, ContinuousLinearMap.bilinearComp_apply]
  rw [← hD v, ← hD w]
  simp only [map_add, add_apply]
  ring
end
end CKSTensorNaturality

end





noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_contDiffAt {γ T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hT : ContDiffAt ℝ ∞ T x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (fun y => leafTensorTrace (γ y) (T y)) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have ht (i j) : ContDiffAt ℝ ∞ (fun y => T y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hT i) j
  have hd : ContDiffAt ℝ ∞ (fun y => determinant (γ y)) x := by
    change ContDiffAt ℝ ∞ (fun y => γ y 0 0 * γ y 1 1 - γ y 0 1 * γ y 1 0) x
    fun_prop
  have hd0 : determinant (γ x) ≠ 0 := by rw [determinant_eq]; exact hp.det_pos.ne'
  have hi (i j) : ContDiffAt ℝ ∞ (fun y => inverse (γ y) i j) x := by
    fin_cases i <;> fin_cases j
    · exact (hc 1 1).div hd hd0
    · exact (hc 0 1).neg.div hd hd0
    · exact (hc 1 0).neg.div hd hd0
    · exact (hc 0 0).div hd hd0
  simp only [leafTensorTrace, ← inverse_eq, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  fun_prop

lemma leafTensorTraceFree_contDiffAt {γ T : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hT : ContDiffAt ℝ ∞ T x) (hp : (γ x).PosDef) :
    ContDiffAt ℝ ∞ (fun y => leafTensorTraceFree (γ y) (T y)) x := by
  have hp' := leafTensorTrace_contDiffAt hγ hT hp
  unfold leafTensorTraceFree
  exact hT.sub ((hp'.div_const 2).smul hγ)

end
end CKSAngularGeometry

end












noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalBaseLapse_eq {r : ℝ} (hr : 0 < r) :
    physicalBaseLapse r = Real.sqrt (1+r^2) := by
  calc
    physicalBaseLapse r = Real.sqrt (r^2)*Real.sqrt (1+(1/r)^2) := by
      rw [Real.sqrt_sq hr.le]; rfl
    _ = Real.sqrt (r^2*(1+(1/r)^2)) := (Real.sqrt_mul (sq_nonneg r) _).symm
    _ = Real.sqrt (1+r^2) := by congr 1; field_simp; ring

variable (U L : PhysicalPoint → ℝ) (γ T : PhysicalPoint → Mat)
    (s η : PhysicalPoint → Point) (x : PhysicalPoint) (w : ℝ)

end
end CKSAngularGeometry

end





noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

def leafBilinear (γ : Mat) : Bilinear PhysicalPoint :=
  ∑ a : Fin 2, ∑ b : Fin 2,
    γ a b • (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj b.succ : PhysicalPoint →L[ℝ] ℝ)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise
lemma leafBilinear_apply (γ : Mat) (v w : PhysicalPoint) :
    leafBilinear γ v w = ∑ a : Fin 2, ∑ b : Fin 2, γ a b*v a.succ*w b.succ := by
  simp [leafBilinear,ContinuousLinearMap.smulRight_apply,mul_assoc]
lemma leafBilinear_apply_basis (γ : Mat) (v : PhysicalPoint) (b : Fin 2) :
    leafBilinear γ v (CKSRealizedRound.basis b.succ) = ∑ a : Fin 2, γ a b*v a.succ := by
  rw [leafBilinear_apply]
  apply Finset.sum_congr rfl
  intro a _
  fin_cases b <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply]
lemma leafBilinear_basis_apply (γ : Mat) (w : PhysicalPoint) (a : Fin 2) :
    leafBilinear γ (CKSRealizedRound.basis a.succ) w = ∑ b : Fin 2, γ a b*w b.succ := by
  rw [leafBilinear_apply]
  fin_cases a <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply]
lemma leafBilinear_basis (γ : Mat) (a b : Fin 2) :
    leafBilinear γ (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ)=γ a b := by
  rw [leafBilinear_apply_basis]
  fin_cases a <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply]
lemma leafBilinear_differentiableAt {γ : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hγ : DifferentiableAt ℝ γ x) : DifferentiableAt ℝ (fun y => leafBilinear (γ y)) x := by
  let : IsBoundedSMul ℝ (Bilinear PhysicalPoint) := @NormedSpace.toIsBoundedSMul ℝ (Bilinear PhysicalPoint) _ _ _
  unfold leafBilinear
  let T := fun (a b : Fin 2) =>
    (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj b.succ : PhysicalPoint →L[ℝ] ℝ)
  exact DifferentiableAt.fun_sum (u := Finset.univ)
    (A := fun a y => ∑ b : Fin 2, γ y a b • T a b) fun a _ =>
      DifferentiableAt.fun_sum (u := Finset.univ)
        (A := fun b y => γ y a b • T a b) fun b _ =>
          (differentiableAt_pi.mp (differentiableAt_pi.mp hγ a) b).smul_const (T a b)
lemma radialFlow_succ (s : PhysicalPoint → Point) (x : PhysicalPoint) (a : Fin 2) :
    radialFlow s x a.succ = -s x a := by
  fin_cases a <;> simp [radialFlow,Fin.sum_univ_two,CKSRealizedRound.basis]
lemma radialFlow_differentiableAt {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hs : DifferentiableAt ℝ s x) : DifferentiableAt ℝ (radialFlow s) x := by
  apply DifferentiableAt.sub (differentiableAt_const _)
  exact DifferentiableAt.fun_sum fun a _ => (differentiableAt_pi.mp hs a).smul_const _
lemma fderiv_radialFlow_succ {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hs : DifferentiableAt ℝ s x) (v : PhysicalPoint) (a : Fin 2) :
    (fderiv ℝ (radialFlow s) x v) a.succ = -fderiv ℝ (fun y => s y a) x v := by
  have h := fderiv_fun_comp x
    (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).differentiableAt
    (radialFlow_differentiableAt hs)
  have he : (fun y => (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ) (radialFlow s y)) =
      (fun y => -s y a) := funext (fun y => radialFlow_succ s y a)
  rw [he,fderiv_fun_neg] at h
  simpa only [ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,neg_apply] using
    (congrArg (fun A : PhysicalPoint →L[ℝ] ℝ => A v) h).symm
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSTensorNaturality CKSCalculus
open scoped BigOperators Matrix.Norms.Elementwise

theorem leafRadialRate_eq_tensorLie {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : DifferentiableAt ℝ γ x) (hs : DifferentiableAt ℝ s x)
    (a b : Fin 2) :
    leafRadialRate γ s x a b = tensorLie (fun y => leafBilinear (γ y)) (radialFlow s) x
      (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) := by
  have hd : (fderiv ℝ (fun y => leafBilinear (γ y)) x (radialFlow s x))
      (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) =
      D (CKSRealizedRound.basis 0) (fun y => γ y a b) x-
        ∑ c : Fin 2, s x c*D (CKSRealizedRound.basis c.succ) (fun y => γ y a b) x := by
    rw [← fderiv_bilinear_const (leafBilinear_differentiableAt hγ)]
    simp only [leafBilinear_basis,radialFlow,D,map_sub,map_sum,map_smul,smul_eq_mul]
  unfold tensorLie
  rw [hd,leafBilinear_apply_basis,leafBilinear_basis_apply]
  simp only [fderiv_radialFlow_succ hs]
  simp only [leafRadialRate,D,Finset.sum_add_distrib,mul_neg,Finset.sum_neg_distrib]
  ring
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix

def angularBlock (A : Mat) : AmbientMat :=
  !![1,0,0;0,A 0 0,A 0 1;0,A 1 0,A 1 1]

def angularCongruence (A γ : Mat) : Mat := A.transpose * γ * A

def angularCovector (A : Mat) (η : Point) : Point := A.transpose *ᵥ η
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix
lemma foliationMetric_covariant (A : Mat) (U : ℝ) {γ : Mat}
    (hγ : γ.IsHermitian) (s : Point) :
    foliationMetric U (angularCongruence A γ) s =
      (angularBlock A).transpose * foliationMetric U γ (A *ᵥ s) * angularBlock A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [foliationMetric, angularCongruence, angularBlock, metricBlock, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, transpose_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
      hermitian_real_symmetry hγ 0 1] <;> ring
lemma foliationTensor_covariant (A : Mat) (U L : ℝ) (η : Point) {T : Mat}
    (hT : T.IsHermitian) (s : Point) :
    foliationTensor U L (angularCovector A η) (angularCongruence A T) s =
      (angularBlock A).transpose * foliationTensor U L η T (A *ᵥ s) * angularBlock A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [foliationTensor, angularCovector, angularCongruence, angularBlock, metricBlock,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, transpose_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.head_fin_const, zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
      hermitian_real_symmetry hT 0 1] <;> ring

lemma angularCongruence_inverse (A γ : Mat) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    (angularCongruence A γ)⁻¹ = A⁻¹ * γ⁻¹ * A.transpose⁻¹ := by
  apply Matrix.inv_eq_left_inv
  have hAt : IsUnit A.transpose.det := by simpa using hA
  simp only [angularCongruence, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hAt]
  rw [← Matrix.mul_assoc γ⁻¹, Matrix.nonsing_inv_mul _ hγ, Matrix.one_mul]
  exact Matrix.nonsing_inv_mul _ hA
lemma leafTensorTrace_covariant (A γ T : Mat) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    leafTensorTrace (angularCongruence A γ) (angularCongruence A T) = leafTensorTrace γ T := by
  rw [leafTensorTrace, angularCongruence_inverse A γ hA hγ]
  have hAt : IsUnit A.transpose.det := by simpa using hA
  change (A⁻¹ * γ⁻¹ * A.transpose⁻¹ * (A.transpose * T * A)).trace = _
  have he : A⁻¹ * γ⁻¹ * A.transpose⁻¹ * (A.transpose * T * A) = A⁻¹ * (γ⁻¹*T) * A := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hAt]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
  rfl
theorem leaf_trace_covariant (A γ T : Mat) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    leafTensorTrace (angularCongruence A γ) (angularCongruence A T) = leafTensorTrace γ T ∧
    leafTensorTraceFree (angularCongruence A γ) (angularCongruence A T) =
      angularCongruence A (leafTensorTraceFree γ T) := by
  refine ⟨leafTensorTrace_covariant A γ T hA hγ, ?_⟩
  unfold leafTensorTraceFree
  rw [leafTensorTrace_covariant A γ T hA hγ]
  simp only [angularCongruence, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSAngularSlice CKSMixedGeometry

def angularMetricPullback (φ : Point → Point) (γ : PhysicalPoint → Mat)
    (x : PhysicalPoint) : Mat := angularCongruence (angularJacobian φ x) (γ (angularChange φ x))
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

lemma angularChange_contDiffAt {φ : Point → Point} {x : PhysicalPoint} {n : WithTop ℕ∞}
    (hφ : ContDiffAt ℝ n φ (angularProjection x)) : ContDiffAt ℝ n (angularChange φ) x := by
  have hr : ContDiffAt ℝ n (fun y : PhysicalPoint => (Pi.single 0 (y 0) : PhysicalPoint)) x := by
    apply contDiffAt_pi.2
    intro i
    by_cases hi : i=0
    · subst i
      change ContDiffAt ℝ n (fun y : PhysicalPoint => y 0) x
      fun_prop
    · simp only [Pi.single_apply, hi, ite_false]
      exact contDiffAt_const
  exact hr.add (injection.contDiff.contDiffAt.comp x (hφ.comp x angularProjection.contDiff.contDiffAt))
lemma angularChange_differentiableAt {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) : DifferentiableAt ℝ (angularChange φ) x := by
  have hr : DifferentiableAt ℝ (fun y : PhysicalPoint => (Pi.single 0 (y 0) : PhysicalPoint)) x := by
    apply differentiableAt_pi.2
    intro i
    by_cases hi : i=0
    · subst i
      change DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) x
      fun_prop
    · simp only [Pi.single_apply, hi, ite_false]
      exact differentiableAt_const _
  exact hr.add (injection.differentiableAt.comp x (hφ.comp x angularProjection.differentiableAt))
lemma fderiv_angularChange_zero {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) (v : PhysicalPoint) :
    fderiv ℝ (angularChange φ) x v 0 = v 0 := by
  have h := congrArg (fun A : PhysicalPoint →L[ℝ] ℝ => A v)
    (fderiv_fun_comp x (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).differentiableAt
      (angularChange_differentiableAt hφ))
  have hp : fderiv ℝ (fun y : PhysicalPoint => y 0) x = ContinuousLinearMap.proj 0 :=
    (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).fderiv
  simpa only [ContinuousLinearMap.proj_apply, angularChange_zero, hp, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply] using h.symm
lemma fderiv_angularChange_succ {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) (v : PhysicalPoint) (a : Fin 2) :
    fderiv ℝ (angularChange φ) x v a.succ = fderiv ℝ φ (angularProjection x) (angularProjection v) a := by
  have h := congrArg (fun A : PhysicalPoint →L[ℝ] ℝ => A v)
    (fderiv_fun_comp x (ContinuousLinearMap.proj a.succ : PhysicalPoint →L[ℝ] ℝ).differentiableAt
      (angularChange_differentiableAt hφ))
  simp only [ContinuousLinearMap.proj_apply, angularChange_succ,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply] at h
  have hd := fderiv_fun_comp x (differentiableAt_pi.mp hφ a) angularProjection.differentiableAt
  rw [hd, ContinuousLinearMap.fderiv] at h
  simpa only [ContinuousLinearMap.comp_apply,fderiv_apply hφ,
    ContinuousLinearMap.proj_apply] using h.symm
lemma angularJacobian_mulVec (φ : Point → Point) (x : PhysicalPoint) (v : Point) :
    angularJacobian φ x *ᵥ v = fderiv ℝ φ (angularProjection x) v := by
  have hv : v = ∑ b : Fin 2, v b • CKSAngularGeometry.basis b := by
    ext a
    fin_cases a <;> simp [CKSAngularGeometry.basis,Pi.single_apply]
  conv_rhs => rw [hv]
  ext a
  simp only [map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, angularJacobian]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma fderiv_angularChange_basis {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) (b : Fin 2) :
    fderiv ℝ (angularChange φ) x (CKSRealizedRound.basis b.succ) =
      ∑ a : Fin 2, angularJacobian φ x a b • CKSRealizedRound.basis a.succ := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [fderiv_angularChange_zero hφ,CKSRealizedRound.basis]
  · rw [fderiv_angularChange_succ hφ]
    have hb : angularProjection (CKSRealizedRound.basis b.succ)=CKSAngularGeometry.basis b := by
      ext c
      simp [angularProjection,CKSRealizedRound.basis,CKSAngularGeometry.basis,Pi.single_apply]
    rw [hb]
    fin_cases a <;> simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply,angularJacobian]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
lemma leafBilinear_congruence (A γ : Mat) (v w : PhysicalPoint) :
    leafBilinear (angularCongruence A γ) v w =
      ∑ a : Fin 2, ∑ b : Fin 2, γ a b * (A *ᵥ angularProjection v) a * (A *ᵥ angularProjection w) b := by
  simp only [leafBilinear_apply, angularCongruence, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_two, angularProjection, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply]
  ring
lemma leafBilinear_angularPullback {φ : Point → Point} (γ : PhysicalPoint → Mat)
    {x : PhysicalPoint} (hφ : DifferentiableAt ℝ φ (angularProjection x)) :
    leafBilinear (angularMetricPullback φ γ x) =
      tensorPullback (angularChange φ) (fun y => leafBilinear (γ y)) x := by
  ext v w
  change leafBilinear (angularCongruence (angularJacobian φ x) (γ (angularChange φ x))) v w =
    leafBilinear (γ (angularChange φ x)) (fderiv ℝ (angularChange φ) x v)
      (fderiv ℝ (angularChange φ) x w)
  rw [leafBilinear_congruence,leafBilinear_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [fderiv_angularChange_succ hφ, fderiv_angularChange_succ hφ,
    angularJacobian_mulVec,angularJacobian_mulVec]

lemma angularProjection_radialFlow (s : PhysicalPoint → Point) (x : PhysicalPoint) :
    angularProjection (radialFlow s x) = -s x := by
  ext a
  exact radialFlow_succ s x a
lemma radialFlow_angular_related {φ : Point → Point} {s s' : PhysicalPoint → Point}
    {x : PhysicalPoint} (hφ : DifferentiableAt ℝ φ (angularProjection x))
    (hrel : angularJacobian φ x *ᵥ s' x = s (angularChange φ x)) :
    fderiv ℝ (angularChange φ) x (radialFlow s' x) = radialFlow s (angularChange φ x) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · rw [fderiv_angularChange_zero hφ,radialFlow_zero,radialFlow_zero]
  · rw [fderiv_angularChange_succ hφ,angularProjection_radialFlow,map_neg,
      ← angularJacobian_mulVec,hrel,radialFlow_succ]
    rfl
lemma tensorLie_angular_expansion (T : PhysicalPoint → Bilinear PhysicalPoint)
    (V : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) (A : Mat) (a b : Fin 2) :
    tensorLie T V x (∑ c : Fin 2, A c a • CKSRealizedRound.basis c.succ)
        (∑ d : Fin 2, A d b • CKSRealizedRound.basis d.succ) =
      ∑ c : Fin 2, ∑ d : Fin 2, A c a * tensorLie T V x
        (CKSRealizedRound.basis c.succ) (CKSRealizedRound.basis d.succ) * A d b := by
  simp only [Fin.sum_univ_two,tensorLie,map_add,map_smul,_root_.add_apply,
    _root_.smul_apply,smul_eq_mul]
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry CKSTensorNaturality
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise
lemma leafRadialRate_angular_natural {φ : Point → Point} {γ γ' : PhysicalPoint → Mat}
    {s s' : PhysicalPoint → Point} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hγ : DifferentiableAt ℝ γ (angularChange φ x))
    (hγ' : DifferentiableAt ℝ γ' x)
    (hs : DifferentiableAt ℝ s (angularChange φ x))
    (hs' : DifferentiableAt ℝ s' x)
    (hrelγ : γ' =ᶠ[𝓝 x] angularMetricPullback φ γ)
    (hrels : ∀ᶠ y in 𝓝 x, angularJacobian φ y *ᵥ s' y = s (angularChange φ y)) :
    leafRadialRate γ' s' x = angularCongruence (angularJacobian φ x)
      (leafRadialRate γ s (angularChange φ x)) := by
  have hφd := hφ.differentiableAt (by norm_num)
  have hφev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ (angularProjection y) :=
    angularProjection.continuous.continuousAt.tendsto.eventually
      ((hφ.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num))
  have hT : (fun y => leafBilinear (γ' y)) =ᶠ[𝓝 x]
      tensorPullback (angularChange φ) (fun y => leafBilinear (γ y)) := by
    filter_upwards [hrelγ,hφev] with y hy hdy
    rw [hy,leafBilinear_angularPullback γ hdy]
  have hV : ∀ᶠ y in 𝓝 x, fderiv ℝ (angularChange φ) y (radialFlow s' y) =
      radialFlow s (angularChange φ y) := by
    filter_upwards [hrels,hφev] with y hy hdy
    exact radialFlow_angular_related hdy hy
  ext a b
  rw [leafRadialRate_eq_tensorLie hγ' hs']
  have hLie : tensorLie (fun y => leafBilinear (γ' y)) (radialFlow s') x
      (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) =
      tensorLie (tensorPullback (angularChange φ) (fun y => leafBilinear (γ y))) (radialFlow s') x
        (CKSRealizedRound.basis a.succ) (CKSRealizedRound.basis b.succ) := by
    unfold tensorLie
    rw [hT.fderiv_eq (𝕜 := ℝ),hT.self_of_nhds]
  rw [hLie,tensorLie_natural (angularChange_contDiffAt hφ) (leafBilinear_differentiableAt hγ)
    (radialFlow_differentiableAt hs) (radialFlow_differentiableAt hs') hV,
    fderiv_angularChange_basis hφd,fderiv_angularChange_basis hφd,tensorLie_angular_expansion]
  simp only [← leafRadialRate_eq_tensorLie hγ hs,angularCongruence,Matrix.mul_apply,
    Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem radial_lapse_angular_natural {φ : Point → Point} {γ γ' : PhysicalPoint → Mat}
    {s s' : PhysicalPoint → Point} {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hγ : DifferentiableAt ℝ γ (angularChange φ x))
    (hγ' : DifferentiableAt ℝ γ' x)
    (hs : DifferentiableAt ℝ s (angularChange φ x))
    (hs' : DifferentiableAt ℝ s' x)
    (hrelγ : γ' =ᶠ[𝓝 x] angularMetricPullback φ γ)
    (hrels : ∀ᶠ y in 𝓝 x, angularJacobian φ y *ᵥ s' y = s (angularChange φ y))
    (hA : IsUnit (angularJacobian φ x).det) (hdet : IsUnit (γ (angularChange φ x)).det) :
    radialExpansion γ' s' x = radialExpansion γ s (angularChange φ x) ∧
    radialMassLapse γ' s' (t ∘ angularChange φ) (F ∘ angularChange φ) x =
      radialMassLapse γ s t F (angularChange φ x) := by
  have hD : radialExpansion γ' s' x = radialExpansion γ s (angularChange φ x) := by
    unfold radialExpansion
    rw [hrelγ.self_of_nhds,leafRadialRate_angular_natural hφ hγ hγ' hs hs' hrelγ hrels]
    change x 0/4*leafTensorTrace (angularCongruence (angularJacobian φ x) (γ (angularChange φ x)))
      (angularCongruence (angularJacobian φ x) (leafRadialRate γ s (angularChange φ x))) = _
    rw [leafTensorTrace_covariant _ _ _ hA hdet,angularChange_zero]
  refine ⟨hD,?_⟩
  simp only [radialMassLapse,radialMassRadical,Function.comp_apply,angularChange_zero,hD]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_add (γ A B : Mat) :
    leafTensorTrace γ (A+B) = leafTensorTrace γ A+leafTensorTrace γ B := by
  simp [leafTensorTrace, Matrix.mul_add]

lemma leafTensorTrace_smul (γ A : Mat) (c : ℝ) :
    leafTensorTrace γ (c • A) = c*leafTensorTrace γ A := by
  simp [leafTensorTrace]

lemma leafTensorTrace_self {γ : Mat} (hp : γ.PosDef) : leafTensorTrace γ γ = 2 := by
  rw [leafTensorTrace, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]
  norm_num

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def logPointDerivative (x : PhysicalPoint) : PhysicalPoint →L[ℝ] PhysicalPoint :=
  ContinuousLinearMap.pi (fun i => if i=0 then (x 0)⁻¹ • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

lemma radiusLogPoint_smoothAt {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ radiusLogPoint x := by
  apply contDiffAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    simp only [radiusLogPoint, ite_true]
    have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
    exact hrad.log hr
  · simp only [radiusLogPoint, hi, ite_false]
    fun_prop

lemma radiusLogPoint_hasFDerivAt {x : PhysicalPoint} (hr : x 0 ≠ 0) :
    HasFDerivAt radiusLogPoint (logPointDerivative x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i=0
  · subst i
    simpa [radiusLogPoint, logPointDerivative, Function.comp_def] using
      (Real.hasDerivAt_log hr).comp_hasFDerivAt x
        (ContinuousLinearMap.proj 0 : PhysicalPoint →L[ℝ] ℝ).hasFDerivAt
  · simp only [radiusLogPoint, hi, ite_false]
    exact (ContinuousLinearMap.proj i : PhysicalPoint →L[ℝ] ℝ).hasFDerivAt

lemma logPointDerivative_basis (i : Fin 3) (x : PhysicalPoint) :
    logPointDerivative x (CKSRealizedRound.basis i) =
      (if i=0 then (x 0)⁻¹ else 1) • CKSRealizedRound.basis i := by
  ext j
  by_cases hi : i=0 <;> by_cases hj : j=0
  · subst i; subst j; simp [logPointDerivative, CKSRealizedRound.basis]
  · subst i; simp [logPointDerivative, CKSRealizedRound.basis, hj]
  · subst j; simp [logPointDerivative, CKSRealizedRound.basis, hi, Ne.symm hi]
  · simp [logPointDerivative, CKSRealizedRound.basis, hi, hj]

lemma D_radiusLogPoint (i : Fin 3) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : DifferentiableAt ℝ f (radiusLogPoint x)) :
    D (CKSRealizedRound.basis i) (fun y => f (radiusLogPoint y)) x =
      (if i=0 then (x 0)⁻¹ else 1)*D (CKSRealizedRound.basis i) f (radiusLogPoint x) := by
  unfold D
  change (fderiv ℝ (f ∘ radiusLogPoint) x) _ = _
  rw [fderiv_comp x hf (radiusLogPoint_hasFDerivAt hr).differentiableAt,
    (radiusLogPoint_hasFDerivAt hr).fderiv]
  simp only [ContinuousLinearMap.comp_apply, logPointDerivative_basis,
    map_smul, smul_eq_mul]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

structure LogCollarData.SmoothAt (f : LogCollarData) (x : MP) : Prop where
  sigma : ContDiffAt ℝ ∞ f.sigma x
  metricError : ContDiffAt ℝ ∞ f.metricError x
  shift : ContDiffAt ℝ ∞ f.shift x
  tError : ContDiffAt ℝ ∞ f.tError x
  LError : ContDiffAt ℝ ∞ f.LError x
  massError : ContDiffAt ℝ ∞ f.massError x
  fstar : ContDiffAt ℝ ∞ f.fstar x
  etaDivR : ContDiffAt ℝ ∞ f.etaDivR x
  tauDivR2 : ContDiffAt ℝ ∞ f.tauDivR2 x

lemma LogCollarData.SmoothAt.regularAt {f : LogCollarData} {x : MP}
    (hf : f.SmoothAt x) : f.RegularAt x :=
  ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.metricError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.shift.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.tError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.LError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.massError.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.fstar.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.etaDivR.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.tauDivR2.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

end
end CKSAngularSlice

end


noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Filter CKSBending Set
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma radialLift_smoothAt {h : ℝ → ℝ} {y : MP}
    (hh : ContDiffAt ℝ ∞ h (Real.exp (y 0))) : ContDiffAt ℝ ∞ (radialLift h) y :=
  hh.comp y (by fun_prop)

lemma collarWeight_smoothAt (R : ℝ) (y : MP) :
    ContDiffAt ℝ ∞ (radialLift (roundingWeight R)) y :=
  radialLift_smoothAt (roundingWeight_smooth R).contDiffAt

lemma collarQ_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarQ R f) y :=
  hf.sigma.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.metricError)

lemma collarShift_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarShift R f) y :=
  (contDiffAt_const.sub (collarWeight_smoothAt R y)).smul hf.shift

lemma collarQ_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 3 (collarQ R f) y :=
  hf.sigma.add ((contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).smul hf.metricError)

lemma collarShift_regularAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.RegularAt y) :
    ContDiffAt ℝ 3 (collarShift R f) y :=
  (contDiffAt_const.sub ((collarWeight_smoothAt R y).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).smul hf.shift

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarGamma R f) x :=
  (show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => (y 0)^2) x by fun_prop).smul
    ((collarQ_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr))

lemma physicalCollarShift_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarShift R f) x :=
  (collarShift_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarGamma_regularAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.RegularAt (radiusLogPoint x)) :
    ContDiffAt ℝ 3 (physicalCollarGamma R f) x :=
  (show ContDiffAt ℝ 3 (fun y : PhysicalPoint => (y 0)^2) x by fun_prop).smul
    ((collarQ_regularAt R hf).comp x ((radiusLogPoint_smoothAt hr).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)))

lemma physicalCollarShift_regularAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.RegularAt (radiusLogPoint x)) :
    ContDiffAt ℝ 3 (physicalCollarShift R f) x :=
  (collarShift_regularAt R hf).comp x ((radiusLogPoint_smoothAt hr).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularSlice
noncomputable section
open Matrix CKSAngularGeometry

structure LogCollarData.AngularRelatedAt (φ : AP → AP) (f f' : LogCollarData) (y : MP) : Prop where
  sigma : f'.sigma y = angularCongruence (angularJacobian φ y) (f.sigma (angularChange φ y))
  metricError : f'.metricError y = angularCongruence (angularJacobian φ y) (f.metricError (angularChange φ y))
  shift : angularJacobian φ y *ᵥ f'.shift y = f.shift (angularChange φ y)
  tError : f'.tError y = f.tError (angularChange φ y)
  LError : f'.LError y = f.LError (angularChange φ y)
  massError : f'.massError y = f.massError (angularChange φ y)
  fstar : f'.fstar y = f.fstar (angularChange φ y)
  etaDivR : f'.etaDivR y = angularCovector (angularJacobian φ y) (f.etaDivR (angularChange φ y))
  tauDivR2 : f'.tauDivR2 y = angularCongruence (angularJacobian φ y) (f.tauDivR2 (angularChange φ y))
end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff

lemma angularCongruence_add (A B C : Mat) :
    angularCongruence A (B+C) = angularCongruence A B+angularCongruence A C := by
  simp [angularCongruence,Matrix.mul_add,Matrix.add_mul]
lemma angularCongruence_smul (A B : Mat) (c : ℝ) :
    angularCongruence A (c • B) = c • angularCongruence A B := by
  simp [angularCongruence]
lemma angularCovector_smul (A : Mat) (v : Point) (c : ℝ) :
    angularCovector A (c • v) = c • angularCovector A v := by
  simp only [angularCovector,Matrix.mulVec_smul]
lemma physicalCollarGamma_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarGamma R f' x = angularMetricPullback φ (physicalCollarGamma R f) x := by
  unfold physicalCollarGamma angularMetricPullback collarQ
  rw [h.sigma,h.metricError]
  simp [radialLift,radiusLogPoint,angularCongruence_add,angularCongruence_smul]
lemma physicalCollarShift_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    angularJacobian φ x *ᵥ physicalCollarShift R f' x =
      physicalCollarShift R f (angularChange φ x) := by
  simp only [physicalCollarShift,collarShift,Matrix.mulVec_smul]
  have hs := h.shift
  simp only [angularJacobian_radiusLogPoint,angularChange_radiusLogPoint] at hs
  rw [hs]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarT_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarT R f' x = physicalCollarT R f (angularChange φ x) := by
  unfold physicalCollarT collarT
  rw [h.tError]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarF_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarF R f' x = physicalCollarF R f (angularChange φ x) := by
  unfold physicalCollarF collarF
  rw [h.fstar,h.massError]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarL_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarL R f' x = physicalCollarL R f (angularChange φ x) := by
  unfold physicalCollarL collarL collarLb
  rw [h.LError]
  simp [radialLift,radiusLogPoint]
lemma physicalCollarEta_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarEta R f' x = angularCovector (angularJacobian φ x)
      (physicalCollarEta R f (angularChange φ x)) := by
  unfold physicalCollarEta collarEtaDivR
  rw [h.etaDivR]
  simp [radialLift,radiusLogPoint,angularCovector_smul]
lemma physicalCollarRawTau_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x)) :
    physicalCollarRawTau R f' x = angularCongruence (angularJacobian φ x)
      (physicalCollarRawTau R f (angularChange φ x)) := by
  unfold physicalCollarRawTau
  rw [h.tauDivR2]
  simp [angularCongruence_smul]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma physicalCollarU_angular_covariant {R : ℝ} {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (hr : 0 < x 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.SmoothAt (radiusLogPoint (angularChange φ x)))
    (hf' : f'.SmoothAt (radiusLogPoint x))
    (hrel : ∀ᶠ y in 𝓝 (radiusLogPoint x), f.AngularRelatedAt φ f' y)
    (hA : IsUnit (angularJacobian φ x).det)
    (hγ : (physicalCollarGamma R f (angularChange φ x)).PosDef) :
    physicalCollarU R f' x = physicalCollarU R f (angularChange φ x) := by
  have hr' : angularChange φ x 0 ≠ 0 := by simpa using hr.ne'
  have he : ∀ᶠ y in 𝓝 x, f.AngularRelatedAt φ f' (radiusLogPoint y) :=
    (radiusLogPoint_smoothAt hr.ne').continuousAt.tendsto.eventually hrel
  have hgm : physicalCollarGamma R f' =ᶠ[𝓝 x] angularMetricPullback φ (physicalCollarGamma R f) :=
    he.mono fun y hy => physicalCollarGamma_angular_covariant R hy
  have hsm : ∀ᶠ y in 𝓝 x, angularJacobian φ y *ᵥ physicalCollarShift R f' y =
      physicalCollarShift R f (angularChange φ y) := he.mono fun y hy => physicalCollarShift_angular_covariant R hy
  have hd := (radial_lapse_angular_natural (t := physicalCollarT R f) (F := physicalCollarF R f) hφ
    ((physicalCollarGamma_smoothAt R hr' hf).differentiableAt (by simp))
    ((physicalCollarGamma_smoothAt R hr.ne' hf').differentiableAt (by simp))
    ((physicalCollarShift_smoothAt R hr' hf).differentiableAt (by simp))
    ((physicalCollarShift_smoothAt R hr.ne' hf').differentiableAt (by simp))
    hgm hsm hA (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')).1
  unfold physicalCollarU radialMassLapse radialMassRadical
  rw [hd,physicalCollarT_angular_covariant R he.self_of_nhds,physicalCollarF_angular_covariant R he.self_of_nhds,
    angularChange_zero]
lemma physicalCollarTangential_angular_covariant (R : ℝ) {φ : Point → Point}
    {f f' : LogCollarData} {x : PhysicalPoint}
    (h : f.AngularRelatedAt φ f' (radiusLogPoint x))
    (hA : IsUnit (angularJacobian φ x).det)
    (hγ : (physicalCollarGamma R f (angularChange φ x)).PosDef) :
    physicalCollarTangential R f' x = angularCongruence (angularJacobian φ x)
      (physicalCollarTangential R f (angularChange φ x)) := by
  unfold physicalCollarTangential radialTangential
  rw [physicalCollarT_angular_covariant R h,physicalCollarGamma_angular_covariant R h,
    physicalCollarRawTau_angular_covariant R h]
  dsimp only [angularMetricPullback]
  rw [(leaf_trace_covariant _ _ _ hA (isUnit_iff_ne_zero.mpr hγ.det_pos.ne')).2]
  simp [angularCongruence_add,angularCongruence_smul]
theorem physicalCollar_angular_covariant {R : ℝ} (_hR : 0 < R)
    {φ : Point → Point} {f f' : LogCollarData} {x : PhysicalPoint}
    (hr : 0 < x 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.SmoothAt (radiusLogPoint (angularChange φ x)))
    (hf' : f'.SmoothAt (radiusLogPoint x))
    (hrel : ∀ᶠ y in 𝓝 (radiusLogPoint x), f.AngularRelatedAt φ f' y)
    (hA : IsUnit (angularJacobian φ x).det)
    (hγ : (physicalCollarGamma R f (angularChange φ x)).PosDef)
    (hτ : (physicalCollarRawTau R f (angularChange φ x)).IsHermitian) :
    physicalCollarMetric R f' x = (angularBlock (angularJacobian φ x)).transpose *
      physicalCollarMetric R f (angularChange φ x) * angularBlock (angularJacobian φ x) ∧
    physicalCollarTensor R f' x = (angularBlock (angularJacobian φ x)).transpose *
      physicalCollarTensor R f (angularChange φ x) * angularBlock (angularJacobian φ x) := by
  have h := hrel.self_of_nhds
  have hT : (physicalCollarTangential R f (angularChange φ x)).IsHermitian := by
    unfold physicalCollarTangential radialTangential leafTensorTraceFree
    exact (hγ.isHermitian.smul (by rfl)).add (hτ.sub (hγ.isHermitian.smul (by rfl)))
  constructor
  · unfold physicalCollarMetric
    rw [physicalCollarU_angular_covariant hr hφ hf hf' hrel hA hγ,physicalCollarGamma_angular_covariant R h]
    dsimp only [angularMetricPullback]
    rw [foliationMetric_covariant _ _ hγ.isHermitian,physicalCollarShift_angular_covariant R h]
  · unfold physicalCollarTensor
    rw [physicalCollarU_angular_covariant hr hφ hf hf' hrel hA hγ,physicalCollarL_angular_covariant R h,
      physicalCollarEta_angular_covariant R h,physicalCollarTangential_angular_covariant R h hA hγ,
      foliationTensor_covariant _ _ _ _ hT,physicalCollarShift_angular_covariant R h]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarGamma R f (slice (Real.exp ρ) a) =
      Real.exp ρ^2 • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarGamma, slice_zero, radiusLogPoint_slice, Real.log_exp,
    collarQ_slice]

lemma physicalCollarShift_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarShift R f (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^5) • fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarShift, radiusLogPoint_slice, Real.log_exp]
  rw [← collarShift_slice, smul_smul]
  simp

lemma physicalCollarT_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarT R f (slice (Real.exp ρ) a) =
      1+(1/Real.exp ρ)^3*fieldT (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarT, radiusLogPoint_slice, Real.log_exp]
  rw [← collarT_slice]
  field_simp
  ring

lemma physicalCollarF_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    physicalCollarF R f (slice (Real.exp ρ) a) =
      fieldF (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  simp only [physicalCollarF, radiusLogPoint_slice, Real.log_exp]
  exact collarF_slice R ρ f a

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarGamma_radial (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (i j : Fin 2) :
    D (CKSRealizedRound.basis 0) (fun y => physicalCollarGamma R f y i j)
      (slice (Real.exp ρ) a) =
      2*Real.exp ρ*fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a i j+
        (1/Real.exp ρ^2)*fieldQr (collarParams R (Real.exp ρ)) (f.angular ρ) a i j := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hq : ContDiffAt ℝ 3 (fun y => collarQ R f y i j) (slice ρ a) :=
    contDiffAt_pi.mp (contDiffAt_pi.mp (collarQ_regularAt R hf) i) j
  have hq' : DifferentiableAt ℝ (fun y => collarQ R f y i j)
      (radiusLogPoint (slice (Real.exp ρ) a)) := by
    simpa using hq.differentiableAt (by norm_num)
  have hrad : DifferentiableAt ℝ (fun y : PhysicalPoint => y 0) (slice (Real.exp ρ) a) := by fun_prop
  change D _ (fun y => (y 0)^2*collarQ R f (radiusLogPoint y) i j) _ = _
  erw [D_mul _ (hrad.pow 2) (hq'.comp _ (radiusLogPoint_hasFDerivAt hr).differentiableAt),
    D_pow _ 2 hrad, D_radiusLogPoint 0 hr hq']
  have hder : D (CKSRealizedRound.basis 0) (fun y : PhysicalPoint => y 0)
      (slice (Real.exp ρ) a) = 1 := by
    exact CKSRealizedRound.D_coord 0 0 _
  simp only [ite_true, Pi.pow_apply, Function.comp_apply,
    radiusLogPoint_slice, Real.log_exp, slice_zero,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, hder, mul_one, collarQ_slice]
  rw [← collarQ_radial R ρ hf hσ i j]
  simp only [CKSRealizedRound.basis, CKSMixedGeometry.basis]
  field_simp
  ring

lemma physicalCollarGamma_angular (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (b i j : Fin 2) :
    D (CKSRealizedRound.basis b.succ) (fun y => physicalCollarGamma R f y i j)
      (slice (Real.exp ρ) a) =
      Real.exp ρ^2*D (basis b)
        (fun y => fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y i j) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.RegularAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hg := physicalCollarGamma_regularAt R hr hf'
  erw [← D_slice b (Real.exp ρ) ((contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by norm_num))]
  have he : (fun y => physicalCollarGamma R f (slice (Real.exp ρ) y) i j) =
      fun y => Real.exp ρ^2*fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) y i j := by
    funext y
    rw [physicalCollarGamma_slice]
    rfl
  rw [he]
  have hqa : ContDiffAt ℝ 3 (fun y => fieldQ (collarParams R (Real.exp ρ))
      (f.angular ρ) y i j) a := by
    have hh := (contDiffAt_pi.mp (contDiffAt_pi.mp (collarQ_regularAt R hf) i) j).comp a
      ((slice_smooth ρ).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
    simpa only [Function.comp_def,collarQ_slice] using hh
  exact D_const_mul _ _ (hqa.differentiableAt (by norm_num))

lemma physicalCollarShift_angular (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a)) (b i : Fin 2) :
    D (CKSRealizedRound.basis b.succ) (fun y => physicalCollarShift R f y i)
      (slice (Real.exp ρ) a) =
      (1/Real.exp ρ^5)*D (basis b)
        (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) a := by
  have hr : (slice (Real.exp ρ) a) 0 ≠ 0 := by simp
  have hf' : f.RegularAt (radiusLogPoint (slice (Real.exp ρ) a)) := by simpa using hf
  have hs := physicalCollarShift_regularAt R hr hf'
  erw [← D_slice b (Real.exp ρ) ((contDiffAt_pi.mp hs i).differentiableAt (by norm_num))]
  have he : (fun y => physicalCollarShift R f (slice (Real.exp ρ) y) i) =
      fun y => (1/Real.exp ρ^5)*fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i := by
    funext y
    rw [physicalCollarShift_slice]
    rfl
  rw [he]
  have hsa : ContDiffAt ℝ 3 (fun y => fieldS (collarParams R (Real.exp ρ))
      (f.angular ρ) y i) a := by
    have hh := ((contDiffAt_pi.mp (collarShift_regularAt R hf) i).comp a
      ((slice_smooth ρ).contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).const_smul
        (Real.exp ρ^5)
    have heS : (fun y => fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) y i) =
        fun y => Real.exp ρ^5*collarShift R f (slice ρ y) i := by
      funext y
      rw [← collarShift_slice]
      rfl
    rw [heS]
    exact hh
  exact D_const_mul _ _ (hsa.differentiableAt (by norm_num))

lemma physicalCollarRadialRate (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0) :
    leafRadialRate (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) =
      (2*Real.exp ρ) • fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a+
        (1/Real.exp ρ^2) • fieldC (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  ext i j
  simp only [leafRadialRate, physicalCollarGamma_radial R ρ hf hσ,
    physicalCollarGamma_angular R ρ hf, physicalCollarShift_angular R ρ hf,
    physicalCollarGamma_slice,physicalCollarShift_slice,
    Matrix.add_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  simp only [fieldC,normalizedLie,collarParams,Matrix.cons_val_zero,
    Fin.sum_univ_two]
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafTensorTrace_eq (γ T : Mat) :
    leafTensorTrace γ T = ∑ i, ∑ j, inverse γ i j*T j i := by
  simp only [leafTensorTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, inverse_eq]

lemma leafTensorTrace_metric_smul (γ T : Mat) {c : ℝ} (hc : c ≠ 0) :
    leafTensorTrace (c • γ) T = leafTensorTrace γ T/c := by
  simp only [leafTensorTrace_eq, inverse_smul c γ hc]
  simp only [Fin.sum_univ_two]
  ring

lemma physicalCollarGamma_pos_iff (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef ↔
      (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a).PosDef := by
  rw [physicalCollarGamma_slice]
  constructor
  · intro hp
    have h := hp.smul (show 0 < 1/Real.exp ρ^2 by positivity)
    simpa only [smul_smul,one_div_mul_cancel (by positivity : Real.exp ρ^2 ≠ 0),one_smul] using h
  · intro hp
    exact hp.smul (by positivity)

lemma physicalCollarExpansion_slice (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) =
      lapseDField (1/Real.exp ρ) (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  have hq := (physicalCollarGamma_pos_iff R ρ f a).mp hp
  rw [radialExpansion, physicalCollarRadialRate R ρ hf hσ, physicalCollarGamma_slice,
    leafTensorTrace_metric_smul _ _ (by positivity : Real.exp ρ^2 ≠ 0),
    leafTensorTrace_add,leafTensorTrace_smul,leafTensorTrace_smul,leafTensorTrace_self hq]
  simp only [slice_zero,lapseDField,fieldD,leafTensorTrace_eq]
  field_simp
  ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma leafRadialRate_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x) :
    ContDiffAt ℝ ∞ (leafRadialRate γ s) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hd (k : Fin 3) (i j) : ContDiffAt ℝ ∞
      (D (CKSRealizedRound.basis k) (fun y => γ y i j)) x :=
    contDiffAt_D (hc i j) (by simp) _
  have hsd (k : Fin 3) (i) : ContDiffAt ℝ ∞
      (D (CKSRealizedRound.basis k) (fun y => s y i)) x :=
    contDiffAt_D (hsc i) (by simp) _
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [leafRadialRate,Fin.sum_univ_two]
  fun_prop

lemma radialExpansion_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {x : PhysicalPoint} (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (hp : (γ x).PosDef) : ContDiffAt ℝ ∞ (radialExpansion γ s) x := by
  unfold radialExpansion
  exact ((show ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x by fun_prop).div_const 4).mul
    (leafTensorTrace_contDiffAt hγ (leafRadialRate_smoothAt hγ hs) hp)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma lapseNormalizedField_rad (z : ℝ) (T F d : Point → ℝ) (a : Point) :
    lapseNormalizedField z T F d a =
      Real.sqrt (lapseRadField z T F a)/lapseDField z d a := by
  unfold lapseNormalizedField lapseRadField lapseVField lapseDField
  congr 2
  have h : 1+z^2 ≠ 0 := by positivity
  field_simp
  ring

lemma physicalCollarRadical_slice (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) =
      (1+Real.exp ρ^2)*lapseRadField (1/Real.exp ρ)
        (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
        (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  rw [radialMassRadical,physicalCollarT_slice,physicalCollarF_slice,slice_zero,
    lapse_radical_reconstruction (Real.exp_pos ρ)]
  unfold lapseRadField lapseVField
  congr 2
  ring

lemma physicalCollarRadical_pos_iff (R ρ : ℝ) (f : LogCollarData) (a : Point) :
    0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) ↔
      0 < lapseRadField (1/Real.exp ρ)
        (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
        (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a := by
  rw [physicalCollarRadical_slice,mul_pos_iff_of_pos_left (by positivity : 0 < 1+Real.exp ρ^2)]

lemma physicalCollarU_slice (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef) :
    physicalCollarU R f (slice (Real.exp ρ) a) = physicalBaseLapse (Real.exp ρ)*
      fieldNormalizedLapse (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  rw [physicalCollarU,radialMassLapse,physicalCollarRadical_slice,
    physicalCollarExpansion_slice R ρ hf hσ hp,
    Real.sqrt_mul (by positivity : 0 ≤ 1+Real.exp ρ^2),
    physicalBaseLapse_eq (Real.exp_pos ρ)]
  unfold fieldNormalizedLapse
  rw [lapseNormalizedField_rad]
  simp only [collarParams,Matrix.cons_val_zero]
  ring

end
end CKSAngularGeometry

end











noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma positiveAngular_posDef {q : Mat} (hs : q.IsHermitian) (hp : positiveAngular q) : q.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hs
  intro v hv
  have he : star v ⬝ᵥ (q *ᵥ v) = determinant q/q 1 1*(v 0)^2+
      q 1 1*(v 1+q 0 1/q 1 1*v 0)^2 := by
    simp only [dotProduct,mulVec,Fin.sum_univ_two,star_trivial]
    rw [hermitian_real_symmetry hs 1 0]
    unfold determinant
    rw [hermitian_real_symmetry hs 1 0]
    field_simp [hp.1.ne']
    ring
  rw [he]
  by_cases h0 : v 0=0
  · have h1 : v 1 ≠ 0 := by
      intro hh
      apply hv
      funext i
      fin_cases i <;> simp [h0,hh]
    simp only [h0,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add]
    exact mul_pos hp.1 (sq_pos_of_ne_zero h1)
  · exact add_pos_of_pos_of_nonneg (mul_pos (div_pos hp.2 hp.1) (sq_pos_of_ne_zero h0))
      (mul_nonneg hp.1.le (sq_nonneg _))

lemma positiveAngular_continuousAt {q : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hq : ContinuousAt q x) (hp : positiveAngular (q x)) :
    ∀ᶠ y in 𝓝 x, positiveAngular (q y) := by
  have h1 := ((continuous_apply 1).continuousAt.comp
    ((continuous_apply 1).continuousAt.comp hq)).eventually (Ioi_mem_nhds hp.1)
  have hd := (determinant_smooth.continuous.continuousAt.comp hq).eventually (Ioi_mem_nhds hp.2)
  filter_upwards [h1,hd] with y hy1 hyd
  exact ⟨hy1,hyd⟩

lemma posDef_eventually_of_symmetric {q : PhysicalPoint → Mat} {x : PhysicalPoint}
    (hq : ContinuousAt q x) (hs : ∀ᶠ y in 𝓝 x, (q y).IsHermitian) (hp : (q x).PosDef) :
    ∀ᶠ y in 𝓝 x, (q y).PosDef := by
  have ha : positiveAngular (q x) := ⟨hp.diag_pos,(determinant_eq _).symm ▸ hp.det_pos⟩
  filter_upwards [hs,positiveAngular_continuousAt hq ha] with y hys hyp
  exact positiveAngular_posDef hys hyp

lemma physicalCollarGamma_isHermitian (R : ℝ) (f : LogCollarData) (x : PhysicalPoint)
    (hσ : (f.sigma (radiusLogPoint x)).IsHermitian)
    (he : (f.metricError (radiusLogPoint x)).IsHermitian) :
    (physicalCollarGamma R f x).IsHermitian :=
  (hσ.add (he.smul (by rfl))).smul (by rfl)

lemma physicalCollarGamma_eventually_posDef {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hσ : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.sigma z).IsHermitian)
    (he : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.metricError z).IsHermitian)
    (hp : (physicalCollarGamma R f x).PosDef) :
    ∀ᶠ y in 𝓝 x, (physicalCollarGamma R f y).PosDef := by
  apply posDef_eventually_of_symmetric (physicalCollarGamma_smoothAt R hr hf).continuousAt _ hp
  filter_upwards [(radiusLogPoint_smoothAt hr).continuousAt.tendsto.eventually (hσ.and he)] with y hy
  exact physicalCollarGamma_isHermitian R f y hy.1 hy.2

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_radialExpansion_eq (f : SourceMassFields) (x : Point) :
    radialExpansion (sourceGamma f) (sourceShift f) x=sourceExpansion f x := by
  unfold radialExpansion sourceExpansion
  rw [leafTensorTrace_eq]
  rfl

end
end CKSMixedGeometry

end






noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry

structure SourceTensorFields.AngularRelatedAt (φ : Angle → Angle)
    (f f' : SourceTensorFields) (x : Point) : Prop where
  sigma : f'.base.sigma (angularProjection x) = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.sigma (φ (angularProjection x)))
  mg : f'.base.mg (angularProjection x) = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.mg (φ (angularProjection x)))
  mK : f'.base.mK (angularProjection x) = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.mK (φ (angularProjection x)))
  mr : f'.base.mr (angularProjection x) = f.base.mr (φ (angularProjection x))
  eg : f'.base.eg x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.eg (angularChange φ x))
  ek : f'.base.ek x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
    (f.base.ek (angularChange φ x))
  b : f'.base.b x = angularCovector (CKSAngularGeometry.angularJacobian φ x)
    (f.base.b (angularChange φ x))
  err : f'.base.err x = f.base.err (angularChange φ x)
  kr : f'.kr x = f.kr (angularChange φ x)
  kb : f'.kb x = angularCovector (CKSAngularGeometry.angularJacobian φ x)
    (f.kb (angularChange φ x))
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped Matrix
lemma angular_inverse_mulVec (A γ : Mat) (b : Point) (hA : IsUnit A.det) (hγ : IsUnit γ.det) :
    A *ᵥ ((angularCongruence A γ)⁻¹ *ᵥ angularCovector A b) = γ⁻¹ *ᵥ b := by
  rw [angularCongruence_inverse A γ hA hγ]
  simp only [angularCovector,Matrix.mulVec_mulVec]
  have hAt : IsUnit A.transpose.det := by simpa using hA
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hAt,Matrix.mul_one,← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hA,Matrix.one_mul]
lemma angular_dual_contraction (A : Mat) (b v : Point) :
    angularCovector A b ⬝ᵥ v = b ⬝ᵥ (A *ᵥ v) := by
  unfold angularCovector
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]
lemma angular_bilinear_contraction (A T : Mat) (v w : Point) :
    v ⬝ᵥ (angularCongruence A T *ᵥ w) = (A *ᵥ v) ⬝ᵥ (T *ᵥ (A *ᵥ w)) := by
  unfold angularCongruence
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  rw [dotProduct_comm,← angularCovector,angular_dual_contraction,dotProduct_comm]
lemma angular_covector_tensor (A T : Mat) (v : Point) :
    (angularCongruence A T).transpose *ᵥ v =
      angularCovector A (T.transpose *ᵥ (A *ᵥ v)) := by
  simp only [angularCongruence,Matrix.transpose_mul,Matrix.transpose_transpose,angularCovector,
    Matrix.mulVec_mulVec,Matrix.mul_assoc]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma sourceGamma_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceGamma f'.base x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
      (sourceGamma f.base (angularChange φ x)) := by
  unfold sourceGamma
  rw [h.sigma,h.mg,h.eg]
  simp [angularCongruence_add,angularCongruence_smul]
lemma sourceTangentialK_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceTangentialK f'.base x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
      (sourceTangentialK f.base (angularChange φ x)) := by
  unfold sourceTangentialK
  rw [h.sigma,h.mK,h.ek]
  simp [angularCongruence_add,angularCongruence_smul]
lemma sourceRadialMetric_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceRadialMetric f'.base x = sourceRadialMetric f.base (angularChange φ x) := by
  simp only [sourceRadialMetric,h.mr,h.err,angularProjection_angularChange,angularChange_zero]
lemma sourceRadialK_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) :
    sourceRadialK f' x = sourceRadialK f (angularChange φ x) := by
  simp only [sourceRadialK,h.kr,angularChange_zero]
lemma sourceShift_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    CKSAngularGeometry.angularJacobian φ x *ᵥ sourceShift f'.base x =
      sourceShift f.base (angularChange φ x) := by
  have hs (k : SourceMassFields) (y : Point) : sourceShift k y = (sourceGamma k y)⁻¹ *ᵥ k.b y := by
    ext a
    change (∑ b, inverse (sourceGamma k y) a b*k.b y b) =
      ∑ b, (sourceGamma k y)⁻¹ a b*k.b y b
    rw [inverse_eq]
  rw [hs,hs,sourceGamma_angular h,h.b]
  exact angular_inverse_mulVec _ _ _ hA hγ
lemma sourceSchur_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceSchur f'.base x = sourceSchur f.base (angularChange φ x) := by
  have he (k : SourceMassFields) (y : Point) : sourceSchur k y =
      sourceRadialMetric k y-k.b y ⬝ᵥ sourceShift k y := by
    simp only [sourceSchur,sourceShift,dotProduct,Fin.sum_univ_two]
    ring
  rw [he,he,sourceRadialMetric_angular h,h.b,angular_dual_contraction,sourceShift_angular h hA hγ]
lemma sourceLapse_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceLapse f'.base x = sourceLapse f.base (angularChange φ x) := by
  simp only [sourceLapse,sourceSchur_angular h hA hγ]
lemma sourceT_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceT f'.base x = sourceT f.base (angularChange φ x) := by
  have he (g T : Mat) : traceProduct (inverse g) T = leafTensorTrace g T := by
    rw [leafTensorTrace_eq]; rfl
  simp only [sourceT,he,sourceGamma_angular h,sourceTangentialK_angular h,
    leafTensorTrace_covariant _ _ _ hA hγ]
lemma sourceOriginalL_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceOriginalL f' x = sourceOriginalL f (angularChange φ x) := by
  have he (k : SourceTensorFields) (y : Point) : sourceOriginalL k y = (sourceLapse k.base y)^2 *
      (sourceRadialK k y-2*(k.kb y ⬝ᵥ sourceShift k.base y)+
        sourceShift k.base y ⬝ᵥ (sourceTangentialK k.base y *ᵥ sourceShift k.base y)) := by
    simp only [sourceOriginalL,sourceLapse,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [he,he,sourceLapse_angular h hA hγ,sourceRadialK_angular h,h.kb,
    angular_dual_contraction,sourceTangentialK_angular h,angular_bilinear_contraction,
    sourceShift_angular h hA hγ]
lemma sourceOriginalEta_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceOriginalEta f' x = angularCovector (CKSAngularGeometry.angularJacobian φ x)
      (sourceOriginalEta f (angularChange φ x)) := by
  have he (k : SourceTensorFields) (y : Point) : sourceOriginalEta k y = sourceLapse k.base y •
      (k.kb y-(sourceTangentialK k.base y).transpose *ᵥ sourceShift k.base y) := by
    ext a
    simp only [sourceOriginalEta,sourceLapse,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
      Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Fin.sum_univ_two]
    ring
  rw [he,he,sourceLapse_angular h hA hγ,h.kb,sourceTangentialK_angular h,
    angular_covector_tensor,sourceShift_angular h hA hγ]
  unfold angularCovector
  rw [Matrix.mulVec_smul,Matrix.mulVec_sub]
lemma sourceOriginalTau_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det) :
    sourceOriginalTau f' x = angularCongruence (CKSAngularGeometry.angularJacobian φ x)
      (sourceOriginalTau f (angularChange φ x)) := by
  have he (k : SourceTensorFields) (y : Point) : sourceOriginalTau k y =
      leafTensorTraceFree (sourceGamma k.base y) (sourceTangentialK k.base y) := by
    rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]
    rfl
  rw [he,he,sourceGamma_angular h,sourceTangentialK_angular h]
  exact (leaf_trace_covariant _ _ _ hA hγ).2
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice CKSMixedGeometry
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma angularJacobian_contDiffAt {φ : Point → Point} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ 2 φ (angularProjection x)) :
    ContDiffAt ℝ 1 (angularJacobian φ) x := by
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  have hF := (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply
    (show ContDiffAt ℝ 1 (fun _ : Point => CKSAngularGeometry.basis b) (angularProjection x) from contDiffAt_const)
  exact (contDiffAt_pi.mp hF a).comp x angularProjection.contDiff.contDiffAt
lemma matrix_det_isUnit_eventually {E : Type*} [TopologicalSpace E] {f : E → Mat} {x : E}
    (hc : ContinuousAt f x) (h : IsUnit (f x).det) : ∀ᶠ y in 𝓝 x, IsUnit (f y).det := by
  exact (((continuous_id.matrix_det : Continuous (Matrix.det : Mat → ℝ)).continuousAt.comp hc).eventually_ne
    (isUnit_iff_ne_zero.mp h)).mono fun _ hy => isUnit_iff_ne_zero.mpr hy
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma sourceExpansion_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (hr : x 0 ≠ 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.RegularAt (angularChange φ x)) (hf' : f'.RegularAt x)
    (hrel : ∀ᶠ y in 𝓝 x, f.AngularRelatedAt φ f' y)
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hp : (sourceMetric f.base (angularChange φ x)).PosDef)
    (hp' : (sourceMetric f'.base x).PosDef) :
    sourceExpansion f'.base x = sourceExpansion f.base (angularChange φ x) := by
  have hr' : angularChange φ x 0 ≠ 0 := by simpa using hr
  have hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp).det_pos.ne'
  have hγ' : IsUnit (sourceGamma f'.base x).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp').det_pos.ne'
  have hγε : ∀ᶠ y in 𝓝 x, IsUnit (sourceGamma f.base (angularChange φ y)).det :=
    matrix_det_isUnit_eventually ((sourceGamma_regular hf.base hr').continuousAt.comp
      ((angularChange_contDiffAt hφ).continuousAt)) hγ
  have hAε := matrix_det_isUnit_eventually (angularJacobian_contDiffAt hφ).continuousAt hA
  have hrels : ∀ᶠ y in 𝓝 x, CKSAngularGeometry.angularJacobian φ y *ᵥ sourceShift f'.base y =
      sourceShift f.base (angularChange φ y) := by
    filter_upwards [hrel,hγε,hAε] with y hy hgy hay
    exact sourceShift_angular hy hay hgy
  have hgdet : determinant (sourceGamma f.base (angularChange φ x)) ≠ 0 := by
    rw [determinant_eq]; exact isUnit_iff_ne_zero.mp hγ
  have hgdet' : determinant (sourceGamma f'.base x) ≠ 0 := by
    rw [determinant_eq]; exact isUnit_iff_ne_zero.mp hγ'
  have hd := (radial_lapse_angular_natural (t := sourceT f.base) (F := sourcePhysicalMass f.base) hφ
    ((sourceGamma_regular hf.base hr').differentiableAt (by norm_num))
    ((sourceGamma_regular hf'.base hr).differentiableAt (by norm_num))
    ((sourceShift_regular hf.base hr' hgdet).differentiableAt (by norm_num))
    ((sourceShift_regular hf'.base hr hgdet').differentiableAt (by norm_num))
    (hrel.mono fun y hy => sourceGamma_angular hy) hrels hA hγ).1
  simpa only [source_radialExpansion_eq] using hd
lemma sourcePhysicalMass_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (hr : x 0 ≠ 0) (hφ : ContDiffAt ℝ 2 φ (angularProjection x))
    (hf : f.RegularAt (angularChange φ x)) (hf' : f'.RegularAt x)
    (hrel : ∀ᶠ y in 𝓝 x, f.AngularRelatedAt φ f' y)
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hp : (sourceMetric f.base (angularChange φ x)).PosDef)
    (hp' : (sourceMetric f'.base x).PosDef) :
    sourcePhysicalMass f'.base x = sourcePhysicalMass f.base (angularChange φ x) := by
  have he (k : SourceMassFields) (y : Point) : sourcePhysicalMass k y = y 0/2*
      (1+(y 0*sourceT k y)^2-(sourceLapse k y*sourceExpansion k y)^2) := by
    simp only [sourcePhysicalMass,sourceT,sourceLapse]
    ring
  have hγ : IsUnit (sourceGamma f.base (angularChange φ x)).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp).det_pos.ne'
  rw [he,he,sourceT_angular hrel.self_of_nhds hA hγ,sourceLapse_angular hrel.self_of_nhds hA hγ,
    sourceExpansion_angular hr hφ hf hf' hrel hA hp hp',angularChange_zero]
lemma sourceAspect_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {x : Point}
    (h : f.AngularRelatedAt φ f' x) (hA : IsUnit (CKSAngularGeometry.angularJacobian φ x).det)
    (hσ : IsUnit (f.base.sigma (φ (angularProjection x))).det) :
    sourceAspect f'.base (angularProjection x) = sourceAspect f.base (φ (angularProjection x)) := by
  have he (g T : Mat) : traceProduct (inverse g) T = leafTensorTrace g T := by
    rw [leafTensorTrace_eq]; rfl
  unfold sourceAspect
  rw [he,he,h.sigma,h.mg,h.mK,h.mr,
    ← angularCongruence_smul,← angularCongruence_add,leafTensorTrace_covariant _ _ _ hA hσ]
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set

def angleTransition (P Q : SmoothAngularPatch) (θ : Angle) : Angle := Q.extension (P.param θ)
def angularOverlap (P Q : SmoothAngularPatch) : Set Angle :=
  P.chart.target ∩ P.chart.symm ⁻¹' Q.chart.source
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped Topology
lemma sourceRemainder_leading_limit {j q : ℕ} {R : ℝ} {W : Set Angle}
    {f : Point → ℝ} {M : Angle → ℝ}
    (h : SourceRemainderOn j (q+1) (angularRadialTail R W)
      (fun y => f y-ordinaryLeadingComponent q M y)) {θ : Angle} (hθ : θ ∈ W) :
    Tendsto (fun r : ℝ => r^q * f (slice r θ)) atTop (𝓝 (M θ)) := by
  obtain ⟨B,hB,hb⟩ := h.bound
  have he : ∀ᶠ r : ℝ in atTop, ‖r^q * f (slice r θ) - M θ‖ ≤ B/r := by
    filter_upwards [eventually_gt_atTop (max R 0)] with r hr
    have hr0 : 0<r := lt_of_le_of_lt (le_max_right _ _) hr
    have hrR : R<r := lt_of_le_of_lt (le_max_left _ _) hr
    have hbr := hb (slice r θ) (by exact ⟨by simpa using hrR,by simpa only [angularProjection_slice] using hθ⟩) [] (by simp)
    simp only [scaledIter,slice_zero] at hbr
    have hid : r^q * f (slice r θ)-M θ = r^q*(f (slice r θ)-ordinaryLeadingComponent q M (slice r θ)) := by
      simp only [ordinaryLeadingComponent,slice_zero,angularProjection_slice]
      field_simp
    rw [Real.norm_eq_abs,hid,abs_mul,abs_of_pos (pow_pos hr0 q)]
    calc
      r^q * |f (slice r θ)-ordinaryLeadingComponent q M (slice r θ)| ≤ r^q * (B/r^(q+1)) :=
        mul_le_mul_of_nonneg_left hbr (pow_nonneg hr0.le _)
      _ = B/r := by rw [pow_succ]; field_simp
  have ht : Tendsto (fun r : ℝ => r^q * f (slice r θ)-M θ) atTop (𝓝 0) :=
    squeeze_zero_norm' he (tendsto_const_nhds.div_atTop tendsto_id)
  simpa only [sub_add_cancel,zero_add] using ht.add_const (M θ)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma angularOverlap_open (P Q : SmoothAngularPatch) : IsOpen (angularOverlap P Q) :=
  P.chart.symm.isOpen_inter_preimage Q.chart.open_source
lemma angleTransition_eq_chart {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : angleTransition P Q θ = Q.chart (P.chart.symm θ) :=
  Q.extension_eq _ hθ.2
lemma angleTransition_target {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : angleTransition P Q θ ∈ Q.chart.target := by
  rw [angleTransition_eq_chart hθ]
  exact Q.chart.map_source hθ.2
lemma param_angleTransition {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : Q.param (angleTransition P Q θ) = P.param θ := by
  rw [angleTransition_eq_chart hθ]
  exact Q.param_chart hθ.2
lemma angleTransition_smoothAt {P Q : SmoothAngularPatch} {θ : Angle}
    (hθ : θ ∈ angularOverlap P Q) : ContDiffAt ℝ ∞ (angleTransition P Q) θ := by
  exact (Q.extension_smooth.contDiffAt (Q.isOpen_domain.mem_nhds (Q.source_domain _ hθ.2))).comp θ
    (P.param_contDiffAt hθ.1)
lemma polar_angularTransition_eq {P Q : SmoothAngularPatch} {y : CKSMixedGeometry.Point}
    (hy : angularProjection y ∈ angularOverlap P Q) :
    polarParam Q (angularChange (angleTransition P Q) y) = polarParam P y := by
  simp only [polarParam,angularChange,angularProjection_slice,slice_zero]
  rw [param_angleTransition hy]
lemma polar_angularTransition_eventuallyEq {P Q : SmoothAngularPatch} {y : CKSMixedGeometry.Point}
    (hy : angularProjection y ∈ angularOverlap P Q) :
    (polarParam Q ∘ angularChange (angleTransition P Q)) =ᶠ[𝓝 y] polarParam P := by
  filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
    ((angularOverlap_open P Q).mem_nhds hy)] with z hz
  exact polar_angularTransition_eq hz
lemma polarTensor_angularTransition (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) (a b : CKSMixedGeometry.I) :
    coordinateTensorPullback (angularChange (angleTransition P Q)) (polarTensorComponents Q A) a b y =
      polarTensorComponents P A a b y := by
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  have h := polarTensor_covariance P Q A (angularChange_differentiableAt ht)
    ((polarParam_contDiffAt P hy.1).differentiableAt (by simp))
    ((polarParam_contDiffAt Q (by simpa only [angularChange,angularProjection_slice] using angleTransition_target hy)).differentiableAt (by simp))
    (differentiableAt_id (𝕜 := ℝ)) (polar_angularTransition_eventuallyEq hy) a b
  have hid : spatialTensorPullback (id : E → E) A = A := by
    funext z; ext v w
    simp [spatialTensorPullback,ContinuousLinearMap.bilinearComp]
  rw [hid] at h
  exact h
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice
lemma angularCongruence_entries (J A : Mat) (a b : Fin 2) : angularCongruence J A a b =
    ∑ i : Fin 2, ∑ j : Fin 2, J i a * A i j * J j b := by
  simp [angularCongruence,Matrix.mul_apply,Fin.sum_univ_two]
  ring
lemma fderiv_angularChange_radial {φ : Point → Point} {x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection x)) :
    fderiv ℝ (angularChange φ) x (CKSRealizedRound.basis 0) = CKSRealizedRound.basis 0 := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · exact fderiv_angularChange_zero hφ _
  · rw [fderiv_angularChange_succ hφ]
    have hz : angularProjection (CKSRealizedRound.basis 0) = 0 := by
      ext a; simp [CKSRealizedRound.basis,angularProjection]
    rw [hz,map_zero]
    simp [CKSRealizedRound.basis]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarTensor_angular_radial (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    polarTensorComponents P A 0 0 y =
      polarTensorComponents Q A 0 0 (angularChange (angleTransition P Q) y) := by
  have h := (polarTensor_angularTransition P Q A hy 0 0).symm
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  rw [coordinateTensorPullback_polar (angularChange_differentiableAt ht) Q A 0 0] at h
  change polarTensorComponents P A 0 0 y =
    A _ (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis 0)))
      (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis 0))) at h
  rw [fderiv_angularChange_radial ht] at h
  exact h
lemma polarTensor_angular_tangential (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    (fun a b : Fin 2 => polarTensorComponents P A a.succ b.succ y) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        (fun a b : Fin 2 => polarTensorComponents Q A a.succ b.succ (angularChange (angleTransition P Q) y)) := by
  ext a b
  have h := (polarTensor_angularTransition P Q A hy a.succ b.succ).symm
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  rw [coordinateTensorPullback_polar (angularChange_differentiableAt ht) Q A a.succ b.succ] at h
  change polarTensorComponents P A a.succ b.succ y =
    A _ (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis a.succ)))
      (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis b.succ))) at h
  rw [fderiv_angularChange_basis ht a,fderiv_angularChange_basis ht b] at h
  rw [h]
  refine Eq.trans ?_ (angularCongruence_entries
    (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
    (fun a b => polarTensorComponents Q A a.succ b.succ (angularChange (angleTransition P Q) y)) a b).symm
  simp only [Fin.sum_univ_two,map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,polarTensorComponents,CKSMixedGeometry.basis,CKSRealizedRound.basis]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise Matrix
lemma CKS_tangential_leading_overlap (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {W W' : Set Angle} {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ} {j j' q q' : ℕ}
    (hA : SourceCKSComponents j q (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents j' q' (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    {θ : Angle} (hθ : θ ∈ angularOverlap P Q) (hW : angleTransition P Q θ ∈ W) (hW' : θ ∈ W') :
    (fun a b : Fin 2 => mg' a.succ b.succ θ) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 θ))
        (fun a b : Fin 2 => mg a.succ b.succ (angleTransition P Q θ)) := by
  let J := CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 θ)
  have hl : Tendsto (fun r : ℝ => (fun a b : Fin 2 => r * polarTensorComponents Q A a.succ b.succ
      (slice r (angleTransition P Q θ)))) atTop
      (𝓝 (fun a b : Fin 2 => mg a.succ b.succ (angleTransition P Q θ))) := by
    apply tendsto_pi_nhds.2
    intro a
    apply tendsto_pi_nhds.2
    intro b
    simpa only [pow_one] using sourceRemainder_leading_limit
      (hA.angular a.succ b.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _)) hW
  have hl' : Tendsto (fun r : ℝ => (fun a b : Fin 2 => r * polarTensorComponents P A a.succ b.succ
      (slice r θ))) atTop (𝓝 (fun a b : Fin 2 => mg' a.succ b.succ θ)) := by
    apply tendsto_pi_nhds.2
    intro a
    apply tendsto_pi_nhds.2
    intro b
    simpa only [pow_one] using sourceRemainder_leading_limit
      (hA'.angular a.succ b.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _)) hW'
  have hc : Continuous (angularCongruence J) := by
    unfold angularCongruence
    fun_prop
  have he (r : ℝ) :
      angularCongruence J (fun a b : Fin 2 => r * polarTensorComponents Q A a.succ b.succ (slice r (angleTransition P Q θ))) =
      (fun a b : Fin 2 => r * polarTensorComponents P A a.succ b.succ (slice r θ)) := by
    change angularCongruence J (r • (fun a b : Fin 2 => polarTensorComponents Q A a.succ b.succ (slice r (angleTransition P Q θ)))) =
      r • (fun a b : Fin 2 => polarTensorComponents P A a.succ b.succ (slice r θ))
    refine (angularCongruence_smul J
      (fun a b => polarTensorComponents Q A a.succ b.succ (slice r (angleTransition P Q θ))) r).trans ?_
    congr 1
    have h := polarTensor_angular_tangential P Q A (y := slice r θ)
      (by simpa only [angularProjection_slice] using hθ)
    have hJ : CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice r θ) = J := by
      unfold J
      unfold CKSAngularGeometry.angularJacobian
      rw [angularProjection_slice,angularProjection_slice]
    have hch : angularChange (angleTransition P Q) (slice r θ) = slice r (angleTransition P Q θ) := by
      simp only [angularChange,slice_zero,angularProjection_slice]
    rw [hJ,hch] at h
    exact h.symm
  exact tendsto_nhds_unique hl' ((hc.tendsto _).comp hl |>.congr' (Filter.Eventually.of_forall he))

theorem CKS_angular_leading_overlap (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {W W' : Set Angle} {R R' : ℝ} {mr mr' : Angle → ℝ} {mg mg' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    {j j' : ℕ}
    (hA : SourceCKSComponents j 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents j' 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    {θ : Angle} (hθ : θ ∈ angularOverlap P Q) (hW : angleTransition P Q θ ∈ W) (hW' : θ ∈ W') :
    mr' θ = mr (angleTransition P Q θ) ∧
    (fun a b : Fin 2 => mg' a.succ b.succ θ) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 θ))
        (fun a b : Fin 2 => mg a.succ b.succ (angleTransition P Q θ)) := by
  refine ⟨?_, CKS_tangential_leading_overlap P Q A hA hA' hθ hW hW'⟩
  have hl := sourceRemainder_leading_limit hA.radial hW
  have hl' := sourceRemainder_leading_limit hA'.radial hW'
  apply tendsto_nhds_unique hl'
  apply hl.congr'
  apply Filter.Eventually.of_forall
  intro r
  have h := polarTensor_angular_radial P Q A (y := slice r θ)
    (by simpa only [angularProjection_slice] using hθ)
  simpa only [angularChange,slice_zero,angularProjection_slice] using congrArg (fun z : ℝ => r^5*z) h.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarTensor_angular_mixed (P Q : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    (fun a : Fin 2 => polarTensorComponents P A 0 a.succ y) =
      angularCovector (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        (fun a : Fin 2 => polarTensorComponents Q A 0 a.succ (angularChange (angleTransition P Q) y)) := by
  ext a
  have h := (polarTensor_angularTransition P Q A hy 0 a.succ).symm
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  rw [coordinateTensorPullback_polar (angularChange_differentiableAt ht) Q A 0 a.succ] at h
  change polarTensorComponents P A 0 a.succ y =
    A _ (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis 0)))
      (fderiv ℝ (polarParam Q) _ (fderiv ℝ (angularChange _) y (CKSRealizedRound.basis a.succ))) at h
  rw [fderiv_angularChange_radial ht,fderiv_angularChange_basis ht a] at h
  rw [h]
  simp only [Fin.sum_univ_two,map_add,map_smul,
    smul_eq_mul,polarTensorComponents,CKSMixedGeometry.basis,CKSRealizedRound.basis,
    angularCovector,Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_two]
lemma angularRoundMetric_overlap (P Q : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    angularRoundMetric P.param (angularProjection y) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        (angularRoundMetric Q.param (angleTransition P Q (angularProjection y))) := by
  have ht := (angleTransition_smoothAt hy).differentiableAt (by simp)
  have hq := (Q.param_contDiffAt (angleTransition_target hy)).differentiableAt (by simp)
  have he : (Q.param ∘ angleTransition P Q) =ᶠ[𝓝 (angularProjection y)] P.param := by
    filter_upwards [(angularOverlap_open P Q).mem_nhds hy] with θ hθ
    exact param_angleTransition hθ
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp _ hq ht] at hd
  have hvec (a : Fin 2) :
      fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) =
      ∑ i : Fin 2, CKSAngularGeometry.angularJacobian (angleTransition P Q) y i a •
        fderiv ℝ Q.param (angleTransition P Q (angularProjection y)) (CKSAngularGeometry.basis i) := by
    rw [← hd,ContinuousLinearMap.comp_apply]
    conv_lhs => arg 2; rw [← angular_vector_expansion (fderiv ℝ (angleTransition P Q) (angularProjection y) (CKSAngularGeometry.basis a))]
    simp only [map_sum,map_smul]
    rfl
  ext a b
  dsimp only [angularRoundMetric]
  rw [hvec,hvec,angularCongruence_entries]
  simp only [Fin.sum_univ_two,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,angularRoundMetric]
  ring
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

theorem actual_CKS_fields_angular_related (P Q : SmoothAngularPatch) (A B : SpatialTensor)
    {W W' : Set Angle} {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' mK mK' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents 3 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    (hB : SourceCKSComponents 2 5 (angularRadialTail R W) (polarTensorComponents Q B) (fun _ => 0) mK)
    (hB' : SourceCKSComponents 2 5 (angularRadialTail R' W') (polarTensorComponents P B) (fun _ => 0) mK')
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q)
    (hW : angleTransition P Q (angularProjection y) ∈ W) (hW' : angularProjection y ∈ W') :
    (cksSourceFields (angularRoundMetric Q.param) (polarTensorComponents Q A) (polarTensorComponents Q B) mr mg mK).AngularRelatedAt
      (angleTransition P Q)
      (cksSourceFields (angularRoundMetric P.param) (polarTensorComponents P A) (polarTensorComponents P B) mr' mg' mK') y := by
  obtain ⟨hmr,hmg⟩ := CKS_angular_leading_overlap P Q A hA hA' hy hW hW'
  have hmK := CKS_tangential_leading_overlap P Q B hB hB' hy hW hW'
  have hJ : CKSAngularGeometry.angularJacobian (angleTransition P Q) (slice 1 (angularProjection y)) =
      CKSAngularGeometry.angularJacobian (angleTransition P Q) y := by
    unfold CKSAngularGeometry.angularJacobian
    rw [angularProjection_slice]
  rw [hJ] at hmg hmK
  have hsub (J X Y : CKSAngularGeometry.Mat) :
      angularCongruence J (X-Y) = angularCongruence J X-angularCongruence J Y := by
    simp only [angularCongruence,Matrix.mul_sub,Matrix.sub_mul]
  have hrem (C : SpatialTensor)
      (m m' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ)
      (hm : (fun a b : Fin 2 => m' a.succ b.succ (angularProjection y)) =
        angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
          (fun a b : Fin 2 => m a.succ b.succ (angleTransition P Q (angularProjection y)))) :
      (fun a b : Fin 2 => polarTensorComponents P C a.succ b.succ y - ordinaryLeadingComponent 1 (m' a.succ b.succ) y) =
        angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
          (fun a b : Fin 2 => polarTensorComponents Q C a.succ b.succ (angularChange (angleTransition P Q) y) -
            ordinaryLeadingComponent 1 (m a.succ b.succ) (angularChange (angleTransition P Q) y)) := by
    simp only [ordinaryLeadingComponent,pow_one,angularChange_zero,angularProjection_angularChange]
    change (fun a b : Fin 2 => polarTensorComponents P C a.succ b.succ y) -
        (1/y 0) • (fun a b : Fin 2 => m' a.succ b.succ (angularProjection y)) =
      angularCongruence (CKSAngularGeometry.angularJacobian (angleTransition P Q) y)
        ((fun a b : Fin 2 => polarTensorComponents Q C a.succ b.succ (angularChange (angleTransition P Q) y)) -
          (1/y 0) • (fun a b : Fin 2 => m a.succ b.succ (angleTransition P Q (angularProjection y))))
    rw [polarTensor_angular_tangential P Q C hy,hm]
    let J := CKSAngularGeometry.angularJacobian (angleTransition P Q) y
    let X : CKSAngularGeometry.Mat :=
      fun a b => polarTensorComponents Q C a.succ b.succ (angularChange (angleTransition P Q) y)
    let Y : CKSAngularGeometry.Mat := fun a b => m a.succ b.succ (angleTransition P Q (angularProjection y))
    exact ((hsub J X ((1 / y 0) • Y)).trans
      (congrArg (fun Z : CKSAngularGeometry.Mat => angularCongruence J X - Z)
        (angularCongruence_smul J Y (1 / y 0)))).symm
  refine ⟨?_,hmg,hmK,hmr,hrem A mg mg' hmg,hrem B mK mK' hmK,?_,?_,?_,?_⟩
  · exact angularRoundMetric_overlap P Q hy
  · exact polarTensor_angular_mixed P Q A hy
  · change polarTensorComponents P A 0 0 y - ordinaryLeadingComponent 5 mr' y =
      polarTensorComponents Q A 0 0 (angularChange (angleTransition P Q) y) -
        ordinaryLeadingComponent 5 mr (angularChange (angleTransition P Q) y)
    rw [polarTensor_angular_radial P Q A hy]
    simp only [ordinaryLeadingComponent,angularChange_zero,angularProjection_angularChange,hmr]
  · exact polarTensor_angular_radial P Q B hy
  · exact polarTensor_angular_mixed P Q B hy
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter CKSAngularGeometry
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma actual_angleTransition_isUnit (P Q : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q) :
    IsUnit (CKSAngularGeometry.angularJacobian (angleTransition P Q) y).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hp := (P.roundMetric_posDef hy.1).det_pos
  have ht := congrArg Matrix.det (angularRoundMetric_overlap P Q hy)
  simp only [angularCongruence,Matrix.det_mul,Matrix.det_transpose,hz,mul_zero,zero_mul] at ht
  rw [ht] at hp
  exact lt_irrefl _ hp
lemma actual_CKS_fields_angular_related_eventually (P Q : SmoothAngularPatch) (A B : SpatialTensor)
    {W W' : Set Angle} (hWo : IsOpen W) (hW'o : IsOpen W') {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' mK mK' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents 3 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    (hB : SourceCKSComponents 2 5 (angularRadialTail R W) (polarTensorComponents Q B) (fun _ => 0) mK)
    (hB' : SourceCKSComponents 2 5 (angularRadialTail R' W') (polarTensorComponents P B) (fun _ => 0) mK')
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q)
    (hW : angleTransition P Q (angularProjection y) ∈ W) (hW' : angularProjection y ∈ W') :
    ∀ᶠ z in 𝓝 y,
      (cksSourceFields (angularRoundMetric Q.param) (polarTensorComponents Q A) (polarTensorComponents Q B) mr mg mK).AngularRelatedAt
        (angleTransition P Q)
        (cksSourceFields (angularRoundMetric P.param) (polarTensorComponents P A) (polarTensorComponents P B) mr' mg' mK') z := by
  have ho := angularProjection.continuous.continuousAt.preimage_mem_nhds
    ((angularOverlap_open P Q).mem_nhds hy)
  have hw := ((angleTransition_smoothAt hy).continuousAt.comp angularProjection.continuous.continuousAt).preimage_mem_nhds (hWo.mem_nhds hW)
  have hw' := angularProjection.continuous.continuousAt.preimage_mem_nhds (hW'o.mem_nhds hW')
  filter_upwards [ho,hw,hw'] with z hz hzW hzW'
  exact actual_CKS_fields_angular_related P Q A B hA hA' hB hB' hz hzW hzW'
end
end CKSLorentz

end


noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix Filter CKSAngularGeometry CKSAngularSlice
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma source_log_leading_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y))
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ y).det)
    (hσ : IsUnit (f.base.sigma (φ (angularProjection y))).det) :
    cksLeadingField f'.base.logFields y = cksLeadingField f.base.logFields (angularChange φ y) := by
  rw [source_leading_mass,source_leading_mass]
  dsimp only
  rw [angularProjection_angularChange]
  have hJA : IsUnit (CKSAngularGeometry.angularJacobian φ (logRadiusChart y)).det := by simpa using hA
  have hs : IsUnit (f.base.sigma (φ (angularProjection (logRadiusChart y)))).det := by simpa only [angularProjection_logRadiusChart] using hσ
  simpa only [angularProjection_logRadiusChart] using congrArg (fun z : ℝ => z/4) (sourceAspect_angular h hJA hs)
lemma source_logGamma_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y)) :
    logGamma f'.base.logFields y = angularCongruence (CKSAngularGeometry.angularJacobian φ y)
      (logGamma f.base.logFields (angularChange φ y)) := by
  have hg := sourceGamma_angular h
  rw [angularJacobian_logRadiusChart,angularChange_logRadiusChart,
    congrFun (sourceGamma_pullback f'.base) y,
    congrFun (sourceGamma_pullback f.base) (angularChange φ y)] at hg
  exact hg
lemma source_logSigma_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y)) :
    f'.base.logFields.sigma y = angularCongruence (CKSAngularGeometry.angularJacobian φ y)
      (f.base.logFields.sigma (angularChange φ y)) := by
  simpa only [SourceMassFields.logFields,angularLift,angularProjection_angularChange,
    angularJacobian_logRadiusChart,angularProjection_logRadiusChart] using h.sigma
lemma source_logQError_angular {φ : Angle → Angle} {f f' : SourceTensorFields} {y : Point}
    (h : f.AngularRelatedAt φ f' (logRadiusChart y)) :
    logQError f'.base.logFields y = angularCongruence (CKSAngularGeometry.angularJacobian φ y)
      (logQError f.base.logFields (angularChange φ y)) := by
  rw [logQError_scaled,logQError_scaled,source_logGamma_angular h,source_logSigma_angular h]
  simp only [angularChange_zero,angularCongruence,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_smul,Matrix.smul_mul]
theorem sourceCollarData_angular_related {φ : Angle → Angle} {f f' : SourceTensorFields}
    {y : Point} (hφ : ContDiffAt ℝ 2 φ (angularProjection y))
    (hf : f.RegularAt (angularChange φ (logRadiusChart y)))
    (hf' : f'.RegularAt (logRadiusChart y))
    (hrel : ∀ᶠ x in 𝓝 (logRadiusChart y), f.AngularRelatedAt φ f' x)
    (hA : IsUnit (CKSAngularGeometry.angularJacobian φ y).det)
    (hp : (sourceMetric f.base (angularChange φ (logRadiusChart y))).PosDef)
    (hp' : (sourceMetric f'.base (logRadiusChart y)).PosDef)
    (hσ : IsUnit (f.base.sigma (φ (angularProjection y))).det) :
    (sourceCollarData f.logFields).AngularRelatedAt φ (sourceCollarData f'.logFields) y := by
  have h := hrel.self_of_nhds
  have hJA : IsUnit (CKSAngularGeometry.angularJacobian φ (logRadiusChart y)).det := by simpa using hA
  have hγ : IsUnit (sourceGamma f.base (angularChange φ (logRadiusChart y))).det :=
    isUnit_iff_ne_zero.mpr (metricBlock_leaf_posDef hp).det_pos.ne'
  have hlead := source_log_leading_angular h hA hσ
  have hs := sourceShift_angular h hJA hγ
  have ht := sourceT_angular h hJA hγ
  have hL := sourceOriginalL_angular h hJA hγ
  have hη := sourceOriginalEta_angular h hJA hγ
  have hτ := sourceOriginalTau_angular h hJA hγ
  have hφx : ContDiffAt ℝ 2 φ (angularProjection (logRadiusChart y)) := by simpa only [angularProjection_logRadiusChart] using hφ
  have hr : logRadiusChart y 0 ≠ 0 := by simp [logRadiusChart]
  have hmass := sourcePhysicalMass_angular hr hφx hf hf' hrel hJA hp hp'
  rw [angularChange_logRadiusChart] at hmass hf hp
  rw [sourcePhysicalMass_pullback hf'.base hp',sourcePhysicalMass_pullback hf.base hp] at hmass
  rw [angularChange_logRadiusChart,angularJacobian_logRadiusChart,
    congrFun (sourceShift_pullback f'.base) y,congrFun (sourceShift_pullback f.base) (angularChange φ y)] at hs
  rw [angularChange_logRadiusChart,congrFun (sourceT_pullback f'.base) y,
    congrFun (sourceT_pullback f.base) (angularChange φ y)] at ht
  rw [angularChange_logRadiusChart,congrFun (sourceOriginalL_pullback f') y,
    congrFun (sourceOriginalL_pullback f) (angularChange φ y)] at hL
  rw [angularChange_logRadiusChart,angularJacobian_logRadiusChart,
    congrFun (sourceOriginalEta_pullback f') y,congrFun (sourceOriginalEta_pullback f) (angularChange φ y)] at hη
  rw [angularChange_logRadiusChart,angularJacobian_logRadiusChart,
    congrFun (sourceOriginalTau_pullback f') y,congrFun (sourceOriginalTau_pullback f) (angularChange φ y)] at hτ
  refine ⟨source_logSigma_angular h,source_logQError_angular h,hs,?_,?_,?_,hlead,?_,?_⟩
  · change logT f'.base.logFields y-1=logT f.base.logFields (angularChange φ y)-1
    rw [ht]
  · change logOriginalL _ y-1=logOriginalL _ (angularChange φ y)-1
    rw [hL]
  · change logPhysicalMass f'.base.logFields y-cksLeadingField f'.base.logFields y=
      logPhysicalMass f.base.logFields (angularChange φ y)-cksLeadingField f.base.logFields (angularChange φ y)
    rw [hmass,hlead]
  · change (fun a => logOriginalEta f'.logFields y a/Real.exp (y 0)) =
      angularCovector (CKSAngularGeometry.angularJacobian φ y)
        (fun a => logOriginalEta f.logFields (angularChange φ y) a/Real.exp (angularChange φ y 0))
    have hscale (z : Angle) (r : ℝ) : (fun a => z a/r) = (1/r) • z := by ext a; simp [div_eq_mul_inv,mul_comm]
    rw [hscale,hscale,hη,angularCovector_smul,angularChange_zero]
  · change (fun a b => logOriginalTau f'.logFields y a b/Real.exp (y 0)^2) =
      angularCongruence (CKSAngularGeometry.angularJacobian φ y)
        (fun a b => logOriginalTau f.logFields (angularChange φ y) a b/Real.exp (angularChange φ y 0)^2)
    have hscale (z : Mat) (r : ℝ) : (fun a b => z a b/r) = (1/r) • z := by ext a b; simp [div_eq_mul_inv,mul_comm]
    rw [hscale,hscale,hτ,angularCongruence_smul,angularChange_zero]
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma SourceMassFields.SmoothAt.regularAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x := by
  exact ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.mr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.eg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.b.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.err.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

lemma SourceTensorFields.SmoothAt.regularAt {f : SourceTensorFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x :=
  ⟨hf.base.regularAt,hf.kr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.kb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

lemma inverse_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → Mat} {x : E}
    (hq : ContDiffAt ℝ ∞ q x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => inverse (q y)) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> first
      | exact contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
      | exact (contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _).neg
  · exact determinant_smooth.contDiffAt.comp x hq
  · exact h0

lemma traceProduct_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : E → Mat} {x : E}
    (hq : ContDiffAt ℝ ∞ q x) (hp : ContDiffAt ℝ ∞ p x) :
    ContDiffAt ℝ ∞ (fun y => traceProduct (q y) (p y)) x :=
  ContDiffAt.sum fun i _ => ContDiffAt.sum fun k _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hq i) k).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hp k) i)

lemma sourceGamma_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceGamma f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

lemma sourceTangentialK_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceTangentialK f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mK))).add hf.ek

lemma sourceRadialMetric_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sourceRadialMetric f) y := by
  have hr : ContDiffAt ℝ ∞ (fun z : Point => z 0) y := by fun_prop
  exact ((contDiffAt_const.div (contDiffAt_const.add (hr.pow 2)) (by positivity)).add
    ((angularLift_diff hf.mr).div (hr.pow 5) (pow_ne_zero _ hy))).add hf.err

lemma sourceShift_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceShift f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]; exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_smoothAt (sourceGamma_smoothAt hf hy) h0
  exact contDiffAt_pi.mpr fun a => ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul (contDiffAt_pi.mp hf.b b)

lemma sourceSchur_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceSchur f) y := by
  have h0 : determinant (sourceGamma f y) ≠ 0 := by
    rw [determinant_eq]; exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hi := inverse_smoothAt (sourceGamma_smoothAt hf hy) h0
  exact (sourceRadialMetric_smoothAt hf hy).sub (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hi a) b).mul ((contDiffAt_pi.mp hf.b a).mul (contDiffAt_pi.mp hf.b b)))

lemma sourceLapse_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceLapse f) y := by
  have hs : 0 < sourceSchur f y := metricBlock_schur_positive hp
  exact contDiffAt_const.div ((sourceSchur_smoothAt hf hy hp).sqrt hs.ne') (Real.sqrt_ne_zero'.mpr hs)

lemma sourceExpansion_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceExpansion f) y := by
  have he : sourceExpansion f=radialExpansion (sourceGamma f) (sourceShift f) :=
    funext fun x => (source_radialExpansion_eq f x).symm
  rw [he]
  exact radialExpansion_smoothAt (sourceGamma_smoothAt hf hy) (sourceShift_smoothAt hf hy hp)
    (metricBlock_leaf_posDef hp)

lemma sourceT_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourceT f) y := by
  have he : sourceT f=fun x => leafTensorTrace (sourceGamma f x) (sourceTangentialK f x)/2 := by
    funext x; rw [leafTensorTrace_eq,sourceT]; unfold traceProduct; ring
  rw [he]
  exact (leafTensorTrace_contDiffAt (sourceGamma_smoothAt hf hy) (sourceTangentialK_smoothAt hf hy)
    (metricBlock_leaf_posDef hp)).div_const 2

lemma sourcePhysicalMass_smoothAt {f : SourceMassFields} {y : Point} (hf : f.SmoothAt y) (hy : y 0 ≠ 0)
    (hp : (sourceMetric f y).PosDef) : ContDiffAt ℝ ∞ (sourcePhysicalMass f) y := by
  have he : sourcePhysicalMass f=fun x => x 0/2*(1+(x 0*sourceT f x)^2-
      (sourceLapse f x*sourceExpansion f x)^2) := by
    funext x; unfold sourcePhysicalMass sourceT sourceLapse; ring
  rw [he]
  have hT := sourceT_smoothAt hf hy hp
  have hU := sourceLapse_smoothAt hf hy hp
  have hd := sourceExpansion_smoothAt hf hy hp
  fun_prop

lemma sourceRadialK_smoothAt {f : SourceTensorFields} {y : Point} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (sourceRadialK f) y := by
  have hh : ContDiffAt ℝ ∞ (fun z : Point => 1+(z 0)^2) y := by fun_prop
  exact (contDiffAt_const.div hh (by positivity)).add hf.kr

lemma sourceOriginalL_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalL f) y := by
  have hshift := sourceShift_smoothAt hf.base hy hp
  have hk := sourceTangentialK_smoothAt hf.base hy
  have hU := sourceLapse_smoothAt hf.base hy hp
  exact (hU.pow 2).mul (((sourceRadialK_smoothAt hf).sub (contDiffAt_const.mul
    (ContDiffAt.sum fun a _ => (contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hf.kb a)))).add
      (ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (contDiffAt_pi.mp (contDiffAt_pi.mp hk a) b).mul
        ((contDiffAt_pi.mp hshift a).mul (contDiffAt_pi.mp hshift b))))

lemma sourceOriginalEta_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalEta f) y := by
  have hshift := sourceShift_smoothAt hf.base hy hp
  have hk := sourceTangentialK_smoothAt hf.base hy
  have hU := sourceLapse_smoothAt hf.base hy hp
  apply contDiffAt_pi.mpr
  intro a
  exact hU.mul ((contDiffAt_pi.mp hf.kb a).sub (ContDiffAt.sum fun b _ =>
    (contDiffAt_pi.mp hshift b).mul (contDiffAt_pi.mp (contDiffAt_pi.mp hk b) a)))

lemma sourceOriginalTau_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) (hp : (sourceMetric f.base y).PosDef) :
    ContDiffAt ℝ ∞ (sourceOriginalTau f) y := by
  have he : sourceOriginalTau f=fun x => leafTensorTraceFree (sourceGamma f.base x) (sourceTangentialK f.base x) := by
    funext x; rw [sourceOriginalTau,leafTensorTraceFree,leafTensorTrace_eq]; rfl
  rw [he]
  exact leafTensorTraceFree_contDiffAt (sourceGamma_smoothAt hf.base hy) (sourceTangentialK_smoothAt hf.base hy)
    (metricBlock_leaf_posDef hp)

end
end CKSMixedGeometry

end


noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Filter
open scoped Topology
lemma SourceTensorFields.RegularAt.eventually {f : SourceTensorFields} {y : Point}
    (hf : f.RegularAt y) : ∀ᶠ z in 𝓝 y, f.RegularAt z := by
  filter_upwards [hf.base.eventually,hf.kr.eventually (by norm_num),hf.kb.eventually (by norm_num)] with z hb hr hk
  exact ⟨hb,hr,hk⟩
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

theorem actual_log_collar_angular_related (P Q : SmoothAngularPatch) (A B : SpatialTensor)
    {W W' : Set Angle} (hWo : IsOpen W) (hW'o : IsOpen W') {R R' : ℝ} {mr mr' : Angle → ℝ}
    {mg mg' mK mK' : CKSMixedGeometry.I → CKSMixedGeometry.I → Angle → ℝ}
    (hA : SourceCKSComponents 3 6 (angularRadialTail R W) (polarTensorComponents Q A) mr mg)
    (hA' : SourceCKSComponents 3 6 (angularRadialTail R' W') (polarTensorComponents P A) mr' mg')
    (hB : SourceCKSComponents 2 5 (angularRadialTail R W) (polarTensorComponents Q B) (fun _ => 0) mK)
    (hB' : SourceCKSComponents 2 5 (angularRadialTail R' W') (polarTensorComponents P B) (fun _ => 0) mK')
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ angularOverlap P Q)
    (hW : angleTransition P Q (angularProjection y) ∈ W) (hW' : angularProjection y ∈ W')
    (hf : (spatialSourceFields Q A B mr mg mK).RegularAt
      (angularChange (angleTransition P Q) (logRadiusChart y)))
    (hf' : (spatialSourceFields P A B mr' mg' mK').RegularAt (logRadiusChart y))
    (hp : ∀ᶠ z in 𝓝 (angularChange (angleTransition P Q) (logRadiusChart y)),
      (sourceMetric (spatialSourceFields Q A B mr mg mK).base z).PosDef)
    (hp' : ∀ᶠ z in 𝓝 (logRadiusChart y),
      (sourceMetric (spatialSourceFields P A B mr' mg' mK').base z).PosDef) :
    ∀ᶠ z in 𝓝 y,
      (sourceCollarData (spatialSourceFields Q A B mr mg mK).logFields).AngularRelatedAt
        (angleTransition P Q) (sourceCollarData (spatialSourceFields P A B mr' mg' mK').logFields) z := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x := y)
  have hφ : ContDiffAt ℝ ∞ (angleTransition P Q) (angularProjection (logRadiusChart y)) := by
    simpa only [angularProjection_logRadiusChart] using angleTransition_smoothAt hy
  have ht := (angularChange_contDiffAt hφ).continuousAt.comp hc
  have hov := angularProjection.continuous.continuousAt.preimage_mem_nhds
    ((angularOverlap_open P Q).mem_nhds hy)
  have hw := ((angleTransition_smoothAt hy).continuousAt.comp angularProjection.continuous.continuousAt).preimage_mem_nhds (hWo.mem_nhds hW)
  have hw' := angularProjection.continuous.continuousAt.preimage_mem_nhds (hW'o.mem_nhds hW')
  filter_upwards [ht.tendsto.eventually hf.eventually,hc.tendsto.eventually hf'.eventually,
    ht.tendsto.eventually hp,hc.tendsto.eventually hp',hov,hw,hw'] with z hfr hfr' hpr hpr' hz hzW hzW'
  apply sourceCollarData_angular_related
    ((angleTransition_smoothAt hz).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hfr hfr' ?_ (actual_angleTransition_isUnit P Q hz) hpr hpr' ?_
  · apply actual_CKS_fields_angular_related_eventually P Q A B hWo hW'o hA hA' hB hB'
    · rwa [angularProjection_logRadiusChart]
    · rwa [angularProjection_logRadiusChart]
    · rwa [angularProjection_logRadiusChart]
  · exact isUnit_iff_ne_zero.mpr (Q.roundMetric_posDef (angleTransition_target hz)).det_pos.ne'
end
end CKSLorentz

end

end OAI
end

section
namespace OAI



noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

theorem polar_inverse_differentials (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    polarInverse P (polarParam P y) = y ∧
    ContDiffAt ℝ ∞ (polarInverse P) (polarParam P y) ∧
    (fderiv ℝ (polarInverse P) (polarParam P y)).comp (fderiv ℝ (polarParam P) y) =
      ContinuousLinearMap.id ℝ Point ∧
    (fderiv ℝ (polarParam P) y).comp (fderiv ℝ (polarInverse P) (polarParam P y)) =
      ContinuousLinearMap.id ℝ E := by
  refine ⟨polarInverse_param P hr hy,polarInverse_smoothAt_param P hr hy,
    polarInverse_fderiv_left P hr hy,?_⟩
  ext z
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy z
  have hh := congrArg (fun L : Point →L[ℝ] Point => L v) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hh ⊢
  rw [hh]
end
end CKSLorentz

end




noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology Filter
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators Topology
lemma matrixBilinear_apply (G : Mat) (v w : V) :
    matrixBilinear G v w = ∑ i : Fin 3, ∑ j : Fin 3, G i j * v i * w j := by
  simp [matrixBilinear, mul_assoc]
lemma matrixBilinear_symm {G : Mat} (hG : Matrix.IsHermitian G) (v w : V) :
    matrixBilinear G v w = matrixBilinear G w v := by
  have hs : ∀ i j, G i j = G j i := by
    intro i j
    have h := congrFun (congrFun hG.eq j) i
    change star (G i j) = G j i at h
    simpa only [star_trivial] using h
  simp only [matrixBilinear_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]
  ring
lemma matrixBilinear_pos {G : Mat} (hG : Matrix.PosDef G) {v : V} (hv : v ≠ 0) :
    0 < matrixBilinear G v v := by
  have h := hG.dotProduct_mulVec_pos hv
  simpa [matrixBilinear_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
attribute [local instance] scalarAtlas

end
end CKSTangentCoefficients

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped BigOperators
lemma bilinear_eq_of_coordinate_basis (B C : Point →L[ℝ] Point →L[ℝ] ℝ)
    (h : ∀ i j, B (basis i) (basis j) = C (basis i) (basis j)) : B = C := by
  ext v w
  rw [← sum_coordinate_basis v,← sum_coordinate_basis w]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,h]
lemma polarLift_components (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (i j : I) :
    polarTensorComponents P (polarLift P F) i j y = F y i j := by
  have hi := congrArg (fun L : Point →L[ℝ] Point => L (basis i)) (polarInverse_fderiv_left P hr hy)
  have hj := congrArg (fun L : Point →L[ℝ] Point => L (basis j)) (polarInverse_fderiv_left P hr hy)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi hj
  change matrixBilinear (F (polarInverse P (polarParam P y)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis i)))
    (fderiv ℝ (polarInverse P) (polarParam P y) (fderiv ℝ (polarParam P) y (basis j))) = _
  rw [polarInverse_param P hr hy,hi,hj]
  simp [matrixBilinear,basis,Pi.single_apply]
lemma polarTensor_ext (P : SmoothAngularPatch) {A B : SpatialTensor}
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : ∀ i j, polarTensorComponents P A i j y = polarTensorComponents P B i j y) :
    A (polarParam P y) = B (polarParam P y) := by
  have hh : (A (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) =
      (B (polarParam P y)).bilinearComp (fderiv ℝ (polarParam P) y) (fderiv ℝ (polarParam P) y) :=
    bilinear_eq_of_coordinate_basis _ _ h
  ext v w
  obtain ⟨v,rfl⟩ := polarParam_fderiv_surjective P hr hy v
  obtain ⟨w,rfl⟩ := polarParam_fderiv_surjective P hr hy w
  exact congrArg (fun L : Point →L[ℝ] Point →L[ℝ] ℝ => L v w) hh

theorem polarLift_reconstruction (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ i j, polarTensorComponents P (polarLift P F) i j y = F y i j) ∧
    (∀ A : SpatialTensor, (∀ i j, polarTensorComponents P A i j y = F y i j) →
      polarLift P F (polarParam P y) = A (polarParam P y)) := by
  refine ⟨polarLift_components P F hr hy,?_⟩
  intro A hA
  apply polarTensor_ext P hr hy
  intro i j
  rw [polarLift_components P F hr hy,hA]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set CKSAngularGeometry

theorem polarLift_overlap (P Q : SmoothAngularPatch)
    (F G : CKSMixedGeometry.Point → Matrix CKSMixedGeometry.I CKSMixedGeometry.I ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0)
    (hy : angularProjection y ∈ angularOverlap P Q)
    (hFG : ∀ a b, F y a b = coordinateTensorPullback (angularChange (angleTransition P Q))
      (fun i j z => G z i j) a b y) :
    polarLift P F (polarParam P y) = polarLift Q G (polarParam P y) := by
  apply polarTensor_ext P hr hy.1
  intro a b
  rw [polarLift_components P F hr hy.1,hFG,
    ← polarTensor_angularTransition P Q (polarLift Q G) hy a b]
  have hθ : angularProjection (angularChange (angleTransition P Q) y) ∈ Q.chart.target := by
    simpa only [angularProjection_angularChange] using angleTransition_target hy
  have hr' : 0 < (angularChange (angleTransition P Q) y) 0 := by simpa using hr
  unfold coordinateTensorPullback
  simp only [polarLift_components Q G hr' hθ]
end
end CKSLorentz

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSCalculus
open scoped BigOperators
lemma fderiv_angularChange_entries {φ : Point → Point} {y : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection y)) (i j : Fin 3) :
    fderiv ℝ (angularChange φ) y (CKSMixedGeometry.basis j) i =
      angularBlock (CKSAngularGeometry.angularJacobian φ y) i j := by
  change fderiv ℝ (angularChange φ) y (CKSRealizedRound.basis j) i = _
  refine Fin.cases ?_ (fun a => ?_) j
  · rw [fderiv_angularChange_radial hφ]
    fin_cases i <;> simp [CKSRealizedRound.basis,angularBlock]
  · rw [fderiv_angularChange_basis hφ]
    fin_cases i <;> fin_cases a <;>
      simp [Fin.sum_univ_two,CKSRealizedRound.basis,Pi.single_apply,angularBlock]
lemma coordinateTensorPullback_angularBlock {φ : Point → Point} {y : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ (angularProjection y))
    (G : PhysicalPoint → Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    coordinateTensorPullback (angularChange φ) (fun i j z => G z i j) a b y =
      ((angularBlock (CKSAngularGeometry.angularJacobian φ y)).transpose *
        G (angularChange φ y) * angularBlock (CKSAngularGeometry.angularJacobian φ y)) a b := by
  have hd (i j : Fin 3) : D (CKSMixedGeometry.basis j) (fun z => angularChange φ z i) y =
      angularBlock (CKSAngularGeometry.angularJacobian φ y) i j := by
    simp only [D,fderiv_apply (angularChange_differentiableAt hφ),ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply,fderiv_angularChange_entries hφ]
  simp only [coordinateTensorPullback,hd,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology

theorem physicalCollar_lift_angular_covariant (P Q : SmoothAngularPatch)
    {R : ℝ} (hR : 0 < R) {f f' : LogCollarData} {y : CKSMixedGeometry.Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ angularOverlap P Q)
    (hf : f.SmoothAt (radiusLogPoint (angularChange (angleTransition P Q) y)))
    (hf' : f'.SmoothAt (radiusLogPoint y))
    (hrel : ∀ᶠ z in 𝓝 (radiusLogPoint y), f.AngularRelatedAt (angleTransition P Q) f' z)
    (hγ : (physicalCollarGamma R f (angularChange (angleTransition P Q) y)).PosDef)
    (hτ : (physicalCollarRawTau R f (angularChange (angleTransition P Q) y)).IsHermitian) :
    polarLift P (physicalCollarMetric R f') (polarParam P y) =
      polarLift Q (physicalCollarMetric R f) (polarParam P y) ∧
    polarLift P (physicalCollarTensor R f') (polarParam P y) =
      polarLift Q (physicalCollarTensor R f) (polarParam P y) := by
  have hφ := angleTransition_smoothAt hy
  obtain ⟨hg,hk⟩ := physicalCollar_angular_covariant hR hr
    (hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hf hf' hrel (actual_angleTransition_isUnit P Q hy) hγ hτ
  constructor
  · apply polarLift_overlap P Q _ _ hr hy
    intro a b
    rw [coordinateTensorPullback_angularBlock (hφ.differentiableAt (by simp)),hg]
  · apply polarLift_overlap P Q _ _ hr hy
    intro a b
    rw [coordinateTensorPullback_angularBlock (hφ.differentiableAt (by simp)),hk]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSTangentCoefficients Set
open scoped ContDiff Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.bilNorm
attribute [local instance] OAI.CKSLorentz.bilSpace
attribute [local instance] OAI.CKSLorentz.epNorm
attribute [local instance] OAI.CKSLorentz.epSpace
attribute [local instance] OAI.CKSLorentz.peNorm
attribute [local instance] OAI.CKSLorentz.peSpace
attribute [local instance] OAI.CKSLorentz.eeNorm
attribute [local instance] OAI.CKSLorentz.eeSpace
lemma matrixBilinear_contDiff : ContDiff ℝ ∞ matrixBilinear := by
  unfold matrixBilinear
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((ContinuousLinearMap.proj j : CKSTangentCoefficients.V →L[ℝ] ℝ).contDiff.comp
    (ContinuousLinearMap.proj i : CKSTangentCoefficients.Mat →L[ℝ] CKSTangentCoefficients.V).contDiff).smul contDiff_const
lemma polarLift_smoothAt (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : ContDiffAt ℝ ∞ F y) : ContDiffAt ℝ ∞ (polarLift P F) (polarParam P y) := by
  have hi := polarInverse_smoothAt_param P hr hy
  have hFi : ContDiffAt ℝ ∞ F (polarInverse P (polarParam P y)) := by
    rw [polarInverse_param P hr hy]; exact hF
  have hB := matrixBilinear_contDiff.contDiffAt.comp (polarParam P y) (hFi.comp (polarParam P y) hi)
  have hD := hi.fderiv_right (show (∞ : ℕ∞ω)+1 ≤ ∞ by simp)
  have hf1 : ContDiff ℝ ∞ (fun B : E →L[ℝ] Point →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] Point →L[ℝ] ℝ) →L[ℝ] (Point →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E Point ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  have hf2 : ContDiff ℝ ∞ (fun B : E →L[ℝ] E →L[ℝ] ℝ => B.flip) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
    exact L.contDiff
  exact hf2.contDiffAt.comp _ ((hf1.contDiffAt.comp _ (hB.clm_comp hD)).clm_comp hD)
lemma polarLift_smooth_positive (P : SmoothAngularPatch) (F : Point → Matrix I I ℝ)
    {y : Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (hF : ContDiffAt ℝ ∞ F y) (hp : Matrix.PosDef (F y)) :
    ContDiffAt ℝ ∞ (polarLift P F) (polarParam P y) ∧
    (∀ v w, polarLift P F (polarParam P y) v w = polarLift P F (polarParam P y) w v) ∧
    ∀ v : E, v ≠ 0 → 0 < polarLift P F (polarParam P y) v v := by
  refine ⟨polarLift_smoothAt P F hr hy hF,?_,?_⟩
  · intro v w
    unfold polarLift
    rw [polarInverse_param P hr hy]
    exact matrixBilinear_symm hp.isHermitian _ _
  · intro v hv
    unfold polarLift
    rw [polarInverse_param P hr hy]
    apply matrixBilinear_pos hp
    intro hz
    change fderiv ℝ (polarInverse P) (polarParam P y) v = 0 at hz
    have hh := congrArg (fun L : E →L[ℝ] E => L v) (polar_inverse_differentials P hr hy).2.2.2
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,hz,map_zero] at hh
    exact hv hh.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma source_cksLeading_smoothAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt (logRadiusChart x)) (hs : determinant (f.logFields.sigma x) ≠ 0) :
    ContDiffAt ℝ ∞ (cksLeadingField f.logFields) x := by
  have hσ := hf.sigma
  have hg := hf.mg
  have hk := hf.mK
  have hr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hg hk hr
  have hi := inverse_smoothAt (angularLift_diff hσ) hs
  exact ((contDiffAt_const.mul (angularLift_diff hr)).add
    (contDiffAt_const.mul (traceProduct_smoothAt hi (angularLift_diff hg)))).add
      (contDiffAt_const.mul (traceProduct_smoothAt hi (angularLift_diff hk)))

theorem sourceCollarData_smoothAt {f : SourceTensorFields} {x : Point}
    (hf : f.SmoothAt (logRadiusChart x))
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef)
    (hs : determinant (f.base.logFields.sigma x) ≠ 0) :
    (sourceCollarData f.logFields).SmoothAt x := by
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hc := logRadiusChart_smooth.contDiffAt (x := x)
  have hσ := hf.base.sigma
  rw [angularProjection_logRadiusChart] at hσ
  have hσ' := angularLift_diff hσ
  have hγ := (sourceGamma_smoothAt hf.base hr).comp x hc
  dsimp only [Function.comp_def] at hγ
  rw [sourceGamma_pullback] at hγ
  have hshift := (sourceShift_smoothAt hf.base hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hshift
  rw [sourceShift_pullback] at hshift
  have ht := (sourceT_smoothAt hf.base hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at ht
  rw [sourceT_pullback] at ht
  have hL := (sourceOriginalL_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hL
  rw [sourceOriginalL_pullback] at hL
  have hη := (sourceOriginalEta_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hη
  rw [sourceOriginalEta_pullback] at hη
  have hτ := (sourceOriginalTau_smoothAt hf hr hp.self_of_nhds).comp x hc
  dsimp only [Function.comp_def] at hτ
  rw [sourceOriginalTau_pullback] at hτ
  have heq : logPhysicalMass f.base.logFields =ᶠ[𝓝 x] (fun y => sourcePhysicalMass f.base (logRadiusChart y)) := by
    filter_upwards [hc.continuousAt.tendsto.eventually hf.base.regularAt.eventually,
      hc.continuousAt.tendsto.eventually hp] with y hy hyp
    exact (sourcePhysicalMass_pullback hy hyp).symm
  have hmass := ((sourcePhysicalMass_smoothAt hf.base hr hp.self_of_nhds).comp x hc).congr_of_eventuallyEq heq
  have hlead := source_cksLeading_smoothAt hf.base hs
  have hexp : ContDiffAt ℝ ∞ (fun y : Point => Real.exp (y 0)) x := by fun_prop
  have he : ContDiffAt ℝ ∞ (logQError f.base.logFields) x := by
    have he' : logQError f.base.logFields=fun y =>
        (1/Real.exp (y 0)^2) • logGamma f.base.logFields y-f.base.logFields.sigma y :=
      funext (logQError_scaled f.base.logFields)
    rw [he']
    exact ((contDiffAt_const.div (hexp.pow 2) (by positivity)).smul hγ).sub hσ'
  refine ⟨hσ',he,hshift,ht.sub contDiffAt_const,hL.sub contDiffAt_const,
    hmass.sub hlead,hlead,?_,?_⟩
  · exact contDiffAt_pi.mpr fun a => (contDiffAt_pi.mp hη a).div hexp (Real.exp_ne_zero _)
  · exact contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b =>
      (contDiffAt_pi.mp (contDiffAt_pi.mp hτ a) b).div (hexp.pow 2) (by positivity)

end
end CKSMixedGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma sourceCollar_sigma_radial {f : SourceTensorFields} {x : Point}
    (hf : f.base.RegularAt (logRadiusChart x)) :
    ∀ i j, D (CKSRealizedRound.basis 0)
      (fun z => (sourceCollarData f.logFields).sigma z i j) x=0 := by
  have hs := hf.sigma
  rw [angularProjection_logRadiusChart] at hs
  intro i j
  exact D_angularLift ((contDiffAt_pi.mp (contDiffAt_pi.mp hs i) j).differentiableAt (by norm_num))

lemma sourceCollar_metricError_hermitian {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base (logRadiusChart x)).PosDef)
    (hs : (f.base.sigma (angularProjection x)).IsHermitian) :
    ((sourceCollarData f.logFields).metricError x).IsHermitian := by
  change (logQError f.base.logFields x).IsHermitian
  rw [logQError_scaled]
  have hγ := (metricBlock_leaf_posDef hp).isHermitian
  change (sourceGamma f.base (logRadiusChart x)).IsHermitian at hγ
  rw [congrFun (sourceGamma_pullback f.base) x] at hγ
  exact (hγ.smul (by rfl)).sub hs

lemma sourceCollar_tau_hermitian {f : SourceTensorFields} {x : Point}
    (hp : (sourceMetric f.base (logRadiusChart x)).PosDef)
    (hk : (sourceTangentialK f.base (logRadiusChart x)).IsHermitian) :
    ((sourceCollarData f.logFields).tauDivR2 x).IsHermitian := by
  have he : (sourceCollarData f.logFields).tauDivR2 x=
      (1/Real.exp (x 0)^2) • sourceOriginalTau f (logRadiusChart x) := by
    rw [congrFun (sourceOriginalTau_pullback f) x]
    ext i j
    change logOriginalTau f.logFields x i j / Real.exp (x 0)^2 =
      (1/Real.exp (x 0)^2) * logOriginalTau f.logFields x i j
    ring
  rw [he]
  exact (hk.sub ((metricBlock_leaf_posDef hp).isHermitian.smul (by rfl))).smul (by rfl)

end
end CKSMixedGeometry

end



noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarQ_hermitian {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hσ : (f.sigma (slice ρ a)).IsHermitian)
    (he : (f.metricError (slice ρ a)).IsHermitian) :
    (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a).IsHermitian := by
  have hs' : (f.sigma (radiusLogPoint (slice (Real.exp ρ) a))).IsHermitian := by simpa using hσ
  have he' : (f.metricError (radiusLogPoint (slice (Real.exp ρ) a))).IsHermitian := by simpa using he
  have h := (physicalCollarGamma_isHermitian R f (slice (Real.exp ρ) a) hs' he').smul
    (show star (1/Real.exp ρ^2)=1/Real.exp ρ^2 by rfl)
  rw [physicalCollarGamma_slice,smul_smul,one_div_mul_cancel (by positivity : Real.exp ρ^2 ≠ 0),one_smul] at h
  exact h

lemma physical_collar_pivots {R ρ : ℝ} {f : LogCollarData} {a : Point}
    (hf : f.SmoothAt (slice ρ a))
    (hσ : ∀ᶠ y in 𝓝 (slice ρ a), (f.sigma y).IsHermitian)
    (he : ∀ᶠ y in 𝓝 (slice ρ a), (f.metricError y).IsHermitian)
    (hσD : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hq : positiveAngular (fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) a))
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
      (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a) :
    (∀ᶠ y in 𝓝 (slice (Real.exp ρ) a), (physicalCollarGamma R f y).PosDef) ∧
      0 < radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) (slice (Real.exp ρ) a) ∧
      0 < radialMassRadical (physicalCollarT R f) (physicalCollarF R f) (slice (Real.exp ρ) a) := by
  have hpq := positiveAngular_posDef (physicalCollarQ_hermitian hσ.self_of_nhds he.self_of_nhds) hq
  have hp := (physicalCollarGamma_pos_iff R ρ f a).mpr hpq
  refine ⟨?_,?_,(physicalCollarRadical_pos_iff R ρ f a).mpr hu⟩
  · apply physicalCollarGamma_eventually_posDef (by simp) (by simpa using hf)
      (by simpa using hσ) (by simpa using he) hp
  · rw [physicalCollarExpansion_slice R ρ hf.regularAt hσD hp]
    exact hd

end
end CKSAngularGeometry

end







noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology
 theorem actual_collar_lift_eq {A B : SpatialTensor} (P Q : CollarSourcePatch A B)
    {R : ℝ} (hR : 0 < R) {y : CKSMixedGeometry.Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ angularOverlap P.patch Q.patch)
    (hW : angleTransition P.patch Q.patch (angularProjection y) ∈ Q.region)
    (hW' : angularProjection y ∈ P.region)
    (hf : Q.fields.SmoothAt (angularChange (angleTransition P.patch Q.patch) y))
    (hf' : P.fields.SmoothAt y)
    (hp : ∀ᶠ z in 𝓝 (angularChange (angleTransition P.patch Q.patch) y), (sourceMetric Q.fields.base z).PosDef)
    (hp' : ∀ᶠ z in 𝓝 y, (sourceMetric P.fields.base z).PosDef)
    (hk : (sourceTangentialK Q.fields.base (angularChange (angleTransition P.patch Q.patch) y)).IsHermitian)
    (hγ : (physicalCollarGamma R (sourceCollarData Q.fields.logFields)
      (angularChange (angleTransition P.patch Q.patch) y)).PosDef) :
    P.metric R (polarParam P.patch y) = Q.metric R (polarParam P.patch y) ∧
    P.tensor R (polarParam P.patch y) = Q.tensor R (polarParam P.patch y) := by
  have hrq : 0 < (angularChange (angleTransition P.patch Q.patch) y) 0 := by simpa using hr
  have hrel := actual_log_collar_angular_related P.patch Q.patch A B Q.region_open P.region_open
    Q.metric_CKS P.metric_CKS Q.tensor_CKS P.tensor_CKS
    (y := radiusLogPoint y)
    (by simpa [radiusLogPoint,angularProjection] using hy)
    (by simpa [radiusLogPoint,angularProjection] using hW)
    (by simpa [radiusLogPoint,angularProjection] using hW')
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hf.regularAt)
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hf'.regularAt)
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hp)
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hp')
  have hdetQ : determinant (Q.fields.base.logFields.sigma
      (radiusLogPoint (angularChange (angleTransition P.patch Q.patch) y))) ≠ 0 := by
    rw [determinant_eq]
    simpa [CollarSourcePatch.fields,spatialSourceFields,cksSourceFields,SourceMassFields.logFields,angularLift,radiusLogPoint,angularChange,angularProjection,slice] using (Q.patch.roundMetric_posDef (angleTransition_target hy)).det_pos.ne'
  have hdetP : determinant (P.fields.base.logFields.sigma (radiusLogPoint y)) ≠ 0 := by
    rw [determinant_eq]
    exact (P.patch.roundMetric_posDef hy.1).det_pos.ne'
  have hsf := sourceCollarData_smoothAt
    (show Q.fields.SmoothAt (logRadiusChart (radiusLogPoint (angularChange (angleTransition P.patch Q.patch) y))) by
      simpa only [logRadiusChart_radiusLogPoint hrq] using hf)
    (by simpa only [logRadiusChart_radiusLogPoint hrq] using hp) hdetQ
  have hsf' := sourceCollarData_smoothAt
    (show P.fields.SmoothAt (logRadiusChart (radiusLogPoint y)) by
      simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hf')
    (by simpa only [CollarSourcePatch.fields,logRadiusChart_radiusLogPoint hr] using hp') hdetP
  apply physicalCollar_lift_angular_covariant P.patch Q.patch hR hr hy hsf hsf' hrel hγ
  unfold physicalCollarRawTau
  apply Matrix.IsHermitian.smul _ (by rfl)
  apply sourceCollar_tau_hermitian
  · simpa only [logRadiusChart_radiusLogPoint hrq] using hp.self_of_nhds
  · simpa only [logRadiusChart_radiusLogPoint hrq] using hk
end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma spatialDirection_val {x : E} (hx : x ≠ 0) : (spatialDirection x : E) = normalizeAmbient x := by
  simp [spatialDirection,hx]
lemma spatialDirection_continuousAt {x : E} (hx : x ≠ 0) : ContinuousAt spatialDirection x := by
  have he : (fun y => (spatialDirection y : E)) =ᶠ[𝓝 x] normalizeAmbient := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hx] with y hy
    exact spatialDirection_val hy
  have hc : ContinuousAt (fun y => (spatialDirection y : E)) x := (normalizeAmbient_smooth hx).continuousAt.congr_of_eventuallyEq he
  exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hc

 theorem polarCone_open (P : SmoothAngularPatch) {W : Set Angle} (hW : IsOpen W) :
    IsOpen (polarCone P W) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem
    ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx.1)
    ((spatialDirection_continuousAt hx.1).preimage_mem_nhds ((P.sphereRegion_open hW).mem_nhds hx.2))
lemma polarInverse_direction (P : SmoothAngularPatch) {x : E}
    (hx : x ≠ 0) (hs : spatialDirection x ∈ P.chart.source) :
    polarInverse P x = slice ‖x‖ (P.chart (spatialDirection x)) := by
  unfold polarInverse
  rw [← spatialDirection_val hx,P.extension_eq _ hs]
 theorem polarCone_inverse (P : SmoothAngularPatch) {W : Set Angle} {x : E}
    (hx : x ∈ polarCone P W) :
    0 < (polarInverse P x) 0 ∧ angularProjection (polarInverse P x) ∈ W ∧
    angularProjection (polarInverse P x) ∈ P.chart.target ∧
    polarParam P (polarInverse P x) = x := by
  rw [polarInverse_direction P hx.1 hx.2.1]
  refine ⟨by simpa using norm_pos_iff.mpr hx.1,by
      rw [angularProjection_slice]
      exact hx.2.2,
    by simpa only [angularProjection_slice] using P.chart.map_source hx.2.1,?_⟩
  simp only [polarParam,slice_zero,angularProjection_slice,P.param_chart hx.2.1,
    spatialDirection_val hx.1,normalizeAmbient,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx.1),one_smul]

end
end CKSLorentz

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma CollarSourcePatch.sigma_eventually {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.region) :
    ∀ᶠ z in 𝓝 y, (P.fields.base.sigma (angularProjection z)).IsHermitian := by
  filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
    (P.region_open.mem_nhds hy)] with z hz
  exact (P.patch.roundMetric_posDef (P.region_target hz)).isHermitian
lemma SourceCollarAtlas.positive_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    ∀ᶠ z in 𝓝 y, (sourceMetric (q.patch i).fields.base z).PosDef := by
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy] with z hz
  exact q.source_positive i z hz

lemma slice_exp_log_projection {y : CKSMixedGeometry.Point} (hy : 0 < y 0) :
    slice (Real.exp (Real.log (y 0))) (angularProjection y) = y := by
  rw [Real.exp_log hy,slice_projection]
lemma logRadiusChart_slice_exp (ρ : ℝ) (a : Angle) :
    logRadiusChart (slice ρ a) = slice (Real.exp ρ) a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [logRadiusChart]
  · simp [logRadiusChart,Fin.succ_ne_zero]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma polarCone_overlap (P Q : SmoothAngularPatch) {W Z : Set Angle} {x : E}
    (hP : x ∈ polarCone P W) (hQ : x ∈ polarCone Q Z) :
    angularProjection (polarInverse P x) ∈ angularOverlap P Q ∧
    angleTransition P Q (angularProjection (polarInverse P x)) ∈ Z ∧
    angularChange (angleTransition P Q) (polarInverse P x) = polarInverse Q x := by
  rw [polarInverse_direction P hP.1 hP.2.1,polarInverse_direction Q hQ.1 hQ.2.1]
  simp only [angularProjection_slice]
  have ht : P.chart (spatialDirection x) ∈ angularOverlap P Q := by
    refine ⟨P.chart.map_source hP.2.1,?_⟩
    change P.chart.symm (P.chart (spatialDirection x)) ∈ Q.chart.source
    rw [P.chart.left_inv hP.2.1]
    exact hQ.2.1
  have he : angleTransition P Q (P.chart (spatialDirection x)) = Q.chart (spatialDirection x) := by
    rw [angleTransition_eq_chart ht,P.chart.left_inv hP.2.1]
  exact ⟨ht,he ▸ hQ.2.2,by simp only [angularChange,slice_zero,angularProjection_slice,he]⟩
lemma physicalCollarGamma_pos_of_metric {R : ℝ} {f : LogCollarData} {y : CKSMixedGeometry.Point}
    (h : (physicalCollarMetric R f y).PosDef) : (physicalCollarGamma R f y).PosDef := by
  have hh := h.submatrix (e := Fin.succ) (Fin.succ_injective 2)
  have he : (physicalCollarMetric R f y).submatrix Fin.succ Fin.succ = physicalCollarGamma R f y := by
    ext i j
    exact foliationMetric_angular (physicalCollarU R f y) (physicalCollarGamma R f y) (physicalCollarShift R f y) i j
  rwa [he] at hh
lemma SourceCollarAtlas.compatible {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {R : ℝ} (hR : 0 < R) (hqR : q.radius < R)
    (hregular : ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y)
    {x : E} (hr : R ≤ ‖x‖) (ht : ‖x‖ ≤ 3*R) {i j : ι}
    (hi : x ∈ polarCone (q.patch i).patch (q.patch i).region)
    (hj : x ∈ polarCone (q.patch j).patch (q.patch j).region) :
    (q.patch i).metric R x = (q.patch j).metric R x ∧
    (q.patch i).tensor R x = (q.patch j).tensor R x := by
  let y := polarInverse (q.patch i).patch x
  let z := polarInverse (q.patch j).patch x
  obtain ⟨hyi,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hi
  obtain ⟨hzj,hzw,hzt,hzx⟩ := polarCone_inverse (q.patch j).patch hj
  obtain ⟨hov,hw,he⟩ := polarCone_overlap (q.patch i).patch (q.patch j).patch hi hj
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hzr : z 0 = ‖x‖ := by simp [z,polarInverse]
  have hyold : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rw [hyr]; exact hqR.trans_le hr, hyw⟩
  have hzold : z ∈ angularRadialTail q.radius (q.patch j).region := ⟨by rw [hzr]; exact hqR.trans_le hr, hzw⟩
  have hzreg := hregular j z (by rwa [hzr]) (by rwa [hzr]) hzw
  have hh := actual_collar_lift_eq (q.patch i) (q.patch j) hR hyi hov hw hyw
    (by rw [he]; exact q.source_smooth j z hzold) (q.source_smooth i y hyold)
    (by rw [he]; exact q.positive_eventually j hzold) (q.positive_eventually i hyold)
    (by rw [he]; exact q.source_symmetric j z hzold)
    (by rw [he]; exact physicalCollarGamma_pos_of_metric hzreg.metric_positive)
  rwa [hyx] at hh
lemma SourceCollarAtlas.local_eq {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {R : ℝ} (hR : 0 < R) (hqR : q.radius < R)
    (hregular : ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
      PhysicalRegularAt (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) y)
    {x : E} (hr : R ≤ ‖x‖) (ht : ‖x‖ ≤ 3*R) {i : ι}
    (hi : x ∈ polarCone (q.patch i).patch (q.patch i).region) :
    q.metric R x = (q.patch i).metric R x ∧ q.tensor R x = (q.patch i).tensor R x := by
  exact q.compatible hR hqR hregular hr ht
    ⟨hi.1,Classical.choose_spec (q.covers (spatialDirection x))⟩ hi
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
attribute [local instance] OAI.CKSLorentz.globalCollarEeNorm
attribute [local instance] OAI.CKSLorentz.globalCollarEeSpace

lemma polarLift_symmetric (P : SmoothAngularPatch) (F : CKSMixedGeometry.Point → Matrix CKSMixedGeometry.I CKSMixedGeometry.I ℝ)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (h : (F y).IsHermitian) : ∀ v w, polarLift P F (polarParam P y) v w = polarLift P F (polarParam P y) w v := by
  intro v w
  unfold polarLift
  rw [polarInverse_param P hr hy]
  exact CKSTangentCoefficients.matrixBilinear_symm h _ _

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry Matrix
open CKSAngularGeometry (metricBlock AmbientMat)
lemma cksSourceFields_gamma (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceGamma (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => A a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mg a.succ b.succ (angularProjection y) +
    (A a.succ b.succ y - ordinaryLeadingComponent 1 (mg a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_tangential (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceTangentialK (cksSourceFields σ A B mr mg mK).base y =
      (y 0)^2 • σ (angularProjection y)+Matrix.of (fun a b : Fin 2 => B a.succ b.succ y) := by
  ext a b
  change (y 0)^2 * σ (angularProjection y) a b + 1/(y 0) * mK a.succ b.succ (angularProjection y) +
    (B a.succ b.succ y - ordinaryLeadingComponent 1 (mK a.succ b.succ) y) = _
  simp only [ordinaryLeadingComponent,pow_one,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.of_apply]
  ring
lemma cksSourceFields_radial (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point) :
    sourceRadialMetric (cksSourceFields σ A B mr mg mK).base y =
      1/(1+(y 0)^2)+A 0 0 y := by
  simp only [sourceRadialMetric,cksSourceFields,ordinaryLeadingComponent]
  ring
lemma metricBlock_add_perturbation (a : ℝ) (q : Mat) (A : AmbientMat)
    (hA : A.IsHermitian) :
    metricBlock (a+A 0 0) (fun i => A 0 i.succ)
      (q+Matrix.of (fun i k : Fin 2 => A i.succ k.succ)) = metricBlock a 0 q+A := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [metricBlock]
  all_goals exact CKSAngularGeometry.hermitian_real_symmetry hA _ _

theorem cksSourceFields_reconstruct (σ : Angle → Mat) (A B : I → I → Point → ℝ)
    (mr : Angle → ℝ) (mg mK : I → I → Angle → ℝ) (y : Point)
    (hA : Matrix.IsHermitian (fun i k => A i k y)) (hB : Matrix.IsHermitian (fun i k => B i k y)) :
    sourceMetric (cksSourceFields σ A B mr mg mK).base y =
      cksReference σ y + Matrix.of (fun i k => A i k y) ∧
    sourceTensor (cksSourceFields σ A B mr mg mK) y =
      cksReference σ y + Matrix.of (fun i k => B i k y) := by
  constructor
  · unfold sourceMetric cksReference
    rw [cksSourceFields_gamma,cksSourceFields_radial]
    exact metricBlock_add_perturbation _ _ _ hA
  · unfold sourceTensor cksReference
    rw [cksSourceFields_tangential]
    exact metricBlock_add_perturbation _ _ _ hB
end
end CKSLorentz

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarMetric_normalized (R ρ : ℝ) {f : LogCollarData} {a : Point}
    (hf : f.RegularAt (slice ρ a))
    (hσ : ∀ i j, D (CKSRealizedRound.basis 0) (fun z => f.sigma z i j) (slice ρ a)=0)
    (hp : (physicalCollarGamma R f (slice (Real.exp ρ) a)).PosDef)
    (hu : 0 < lapseRadField (1/Real.exp ρ)
      (fieldT (collarParams R (Real.exp ρ)) (f.angular ρ))
      (fieldF (collarParams R (Real.exp ρ)) (f.angular ρ)) a)
    (hd : 0 < lapseDField (1/Real.exp ρ)
      (fieldD (collarParams R (Real.exp ρ)) (f.angular ρ)) a) :
    radialNormalize (Real.exp ρ) (physicalCollarMetric R f (slice (Real.exp ρ) a))=
      fieldNormalizedMetric (collarParams R (Real.exp ρ)) (f.angular ρ) a := by
  have hn : fieldNormalizedLapse (collarParams R (Real.exp ρ)) (f.angular ρ) a ≠ 0 := by
    unfold fieldNormalizedLapse
    rw [lapseNormalizedField_rad]
    exact div_ne_zero (Real.sqrt_pos.mpr hu).ne' hd.ne'
  unfold physicalCollarMetric
  rw [physicalCollarU_slice R ρ hf hσ hp, physicalCollarGamma_slice,
    physicalCollarShift_slice,physicalBaseLapse_eq (Real.exp_pos ρ)]
  have he : 1/Real.exp ρ^5=(1/Real.exp ρ)^5 := by simp
  rw [he,radialNormalize_foliation (Real.exp_pos ρ) hn]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSCalculus Set Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem source_physical_collar_metric_comparison
    {K : Set CKSMixedGeometry.MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R, R₀ ≤ R → 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ (R : ℝ) (f : SourceTensorFields) (ρ : ℝ) (a : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R →
      f.SmoothAt (logRadiusChart (slice ρ a)) →
      (∀ᶠ y in 𝓝 (logRadiusChart (slice ρ a)), (sourceMetric f.base y).PosDef) →
      (∀ᶠ y in 𝓝 (slice ρ a), (f.base.sigma (angularProjection y)).IsHermitian) →
      matrixThreeJets (angularLift f.base.sigma) (slice ρ a) ∈ K →
      ‖matrixThreeJets (angularLift f.base.sigma) (slice ρ a)‖ ≤ B →
      ‖matrixThreeJets (angularLift f.base.mg) (slice ρ a)‖ ≤ B →
      ‖matrixScalarJets (angularLift f.base.mK) (slice ρ a)‖ ≤ B →
      ‖actualScalarJet (angularLift f.base.mr) (slice ρ a)‖ ≤ B →
      f.ComponentBounds B (logRadiusChart (slice ρ a)) →
      ∀ v : Fin 3 → ℝ,
      l R * quadratic3 (sourceMetric f.base (logRadiusChart (slice ρ a))) v ≤
      quadratic3 (physicalCollarMetric R (sourceCollarData f.logFields)
        (slice (Real.exp ρ) a)) v
 := by
  obtain ⟨R₁,hR₁,l,hl,hlb,hcomp⟩ := source_collar_metric_comparison hK hreg hB
  obtain ⟨R₂,hR₂,hfuture⟩ := source_actual_collar_future_regions hK hreg hB
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),l,hl,?_,?_⟩
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R f ρ a hR hr htop hf hp hσ hmem hs hmg hmk hmr hb
  have hR₁R : R₁ ≤ R := (le_max_left _ _).trans hR
  have hR₂R : R₂ ≤ R := (le_max_right _ _).trans hR
  have hsd : determinant (f.base.logFields.sigma (slice ρ a)) ≠ 0 := by
    rw [determinant_eq]
    exact (hreg _ hmem).det_pos.ne'
  have hsm := sourceCollarData_smoothAt hf hp hsd
  have hσD := sourceCollar_sigma_radial (f := f) hf.base.regularAt
  have he : ∀ᶠ y in 𝓝 (slice ρ a), ((sourceCollarData f.logFields).metricError y).IsHermitian := by
    filter_upwards [logRadiusChart_smooth.continuous.continuousAt.tendsto.eventually hp,hσ] with y hyp hys
    exact sourceCollar_metricError_hermitian hyp hys
  have hregions := (hfuture R f ρ a hR₂R hr htop hf hp hmem hs hmg hmk hmr hb).1
  obtain ⟨hγ,hd,hu⟩ := physical_collar_pivots hsm hσ he hσD hregions.1 hregions.2.1 hregions.2.2
  have hnormalize := physicalCollarMetric_normalized R ρ hsm.regularAt hσD hγ.self_of_nhds
    hregions.2.1 hregions.2.2
  have hmk' := hf.base.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hek' := hf.base.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have h := hcomp R f ρ a hR₁R hr htop hf.regularAt hmk' hek' hp hmem hs hmg hmk hmr hb
  rw [← hnormalize] at h
  exact radialNormalize_comparison (Real.exp_ne_zero ρ) h

end
end CKSMixedGeometry

end


noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma hyperbolicField_apply (x v w : E) : hyperbolicField x v w = hyperbolicMetric x v w := by
  change inner ℝ v w - (1/(1+‖x‖^2)) * (inner ℝ x v * inner ℝ x w) =
    inner ℝ v w - inner ℝ x v * inner ℝ x w / (1+‖x‖^2)
  ring
lemma polarParam_fderiv (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (v : Point) :
    fderiv ℝ (polarParam P) y v = v 0 • P.param (angularProjection y) +
      y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) := by
  have hP := (P.param_contDiffAt hy).differentiableAt (by simp)
  have hp := (ContinuousLinearMap.proj (0:I) : Point →L[ℝ] ℝ).hasFDerivAt (x := y)
  have ha := hP.hasFDerivAt.comp y angularProjection.hasFDerivAt
  have hh := hp.smul ha
  change HasFDerivAt (polarParam P) _ y at hh
  rw [hh.fderiv]
  change y 0 • fderiv ℝ P.param (angularProjection y) (angularProjection v) + v 0 • P.param (angularProjection y) = _
  exact add_comm _ _
lemma polarParam_fderiv_radial (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) :
    fderiv ℝ (polarParam P) y (basis 0) = P.param (angularProjection y) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis 0) = 0 := by ext a; simp [angularProjection,basis,Fin.succ_ne_zero]
  rw [ha]
  simp [basis]
lemma polarParam_fderiv_angular (P : SmoothAngularPatch) {y : Point}
    (hy : angularProjection y ∈ P.chart.target) (a : Fin 2) :
    fderiv ℝ (polarParam P) y (basis a.succ) = y 0 • fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a) := by
  rw [polarParam_fderiv P hy]
  have ha : angularProjection (basis a.succ) = CKSAngularGeometry.basis a := by
    ext b
    simp [angularProjection,basis,CKSAngularGeometry.basis,Pi.single_apply,Fin.succ_inj]
  rw [ha]
  simp [basis,Fin.succ_ne_zero]
lemma hyperbolicField_polar (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (fun i j => polarTensorComponents P hyperbolicField i j y) = cksReference (angularRoundMetric P.param) y := by
  have hn : ‖P.param (angularProjection y)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using P.param_sphere (angularProjection y)
  have hi : inner ℝ (P.param (angularProjection y)) (P.param (angularProjection y)) = 1 := by
    rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have ht := P.param_tangent hy
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy]
      unfold hyperbolicMetric
      rw [polarParam_norm P hr.le]
      simp only [polarParam,real_inner_smul_left,hi,mul_one]
      simp only [cksReference,CKSAngularGeometry.metricBlock]
      change 1 - y 0 * y 0/(1+(y 0)^2) = 1/(1+(y 0)^2)
      have hnz : 1 + (y 0)^2 ≠ 0 := by positivity
      field_simp
      ring
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis 0))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      fin_cases b <;> simp [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,cksReference,CKSAngularGeometry.metricBlock]
  · refine Fin.cases ?_ (fun b => ?_) j
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis 0)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_radial P hy,polarParam_fderiv_angular P hy]
      have hta : inner ℝ (fderiv ℝ P.param (angularProjection y) (CKSAngularGeometry.basis a)) (P.param (angularProjection y)) = 0 := by
        rw [real_inner_comm]; exact ht _
      fin_cases a <;> simp_all [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,cksReference,CKSAngularGeometry.metricBlock]
    · change hyperbolicField (polarParam P y) (fderiv ℝ (polarParam P) y (basis a.succ))
        (fderiv ℝ (polarParam P) y (basis b.succ)) = _
      rw [hyperbolicField_apply,polarParam_fderiv_angular P hy,polarParam_fderiv_angular P hy]
      simp only [hyperbolicMetric,polarParam,real_inner_smul_left,real_inner_smul_right,ht,mul_zero,zero_div,sub_zero]
      fin_cases a <;> fin_cases b <;>
        simp [cksReference,CKSAngularGeometry.metricBlock,angularRoundMetric,pow_two,mul_assoc]

end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry
lemma polarTensorComponents_hermitian (P : SmoothAngularPatch) (A : SpatialTensor)
    (y : CKSMixedGeometry.Point)
    (hA : ∀ v w, A (polarParam P y) v w = A (polarParam P y) w v) :
    Matrix.IsHermitian (fun i j => polarTensorComponents P A i j y) := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  exact hA _ _
lemma polar_sourceSpatial (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    cksReference (angularRoundMetric P.param) y + Matrix.of (fun i j => polarTensorComponents P A i j y) =
      (fun i j => polarTensorComponents P (sourceSpatial A) i j y) := by
  rw [← hyperbolicField_polar P hr hy]
  rfl

theorem spatial_source_reconstruction {A B : SpatialTensor} (P : CollarSourcePatch A B)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.patch.chart.target)
    (hA : ∀ v w, A (polarParam P.patch y) v w = A (polarParam P.patch y) w v)
    (hB : ∀ v w, B (polarParam P.patch y) v w = B (polarParam P.patch y) w v) :
    sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) ∧
    sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) ∧
    polarLift P.patch (sourceMetric P.fields.base) (polarParam P.patch y) = sourceSpatial A (polarParam P.patch y) ∧
    polarLift P.patch (sourceTensor P.fields) (polarParam P.patch y) = sourceSpatial B (polarParam P.patch y) := by
  obtain ⟨hg,hk⟩ := cksSourceFields_reconstruct (angularRoundMetric P.patch.param)
    (polarTensorComponents P.patch A) (polarTensorComponents P.patch B) P.mr P.mg P.mK y
    (polarTensorComponents_hermitian P.patch A y hA) (polarTensorComponents_hermitian P.patch B y hB)
  have heg : sourceMetric P.fields.base y = (fun i j => polarTensorComponents P.patch (sourceSpatial A) i j y) :=
    hg.trans (polar_sourceSpatial P.patch A hr hy)
  have hek : sourceTensor P.fields y = (fun i j => polarTensorComponents P.patch (sourceSpatial B) i j y) :=
    hk.trans (polar_sourceSpatial P.patch B hr hy)
  refine ⟨heg,hek,?_,?_⟩
  · apply (polarLift_reconstruction P.patch (sourceMetric P.fields.base) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) heg.symm
  · apply (polarLift_reconstruction P.patch (sourceTensor P.fields) hr hy).2
    intro i j
    exact congrArg (fun F : AmbientMat => F i j) hek.symm
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
lemma SourceCollarAtlas.eventually_local_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ,
      Tendsto l atTop (𝓝 1) ∧ (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ i y, R ≤ y 0 → y 0 ≤ 3*R → angularProjection y ∈ (q.patch i).region →
        ∀ v : Fin 3 → ℝ,
        l R * quadratic3 (sourceMetric (q.patch i).fields.base y) v ≤
          quadratic3 (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) y) v := by
  obtain ⟨R₁,hR₁,l,hl,hlb,hcomp⟩ := source_physical_collar_metric_comparison
    q.jetSet_compact q.jetSet_positive q.bound_nonneg
  refine ⟨max R₁ (q.radius+1),hR₁.trans (le_max_left _ _),?_,l,hl,?_,?_⟩
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R hR i y hr ht hw v
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans hR
  have hr0 : 0 < y 0 := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)) hr
  have hrad : q.radius < y 0 := lt_of_lt_of_le
    ((show q.radius < q.radius+1 by linarith).trans_le ((le_max_right _ _).trans hR)) hr
  have hx : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨hrad,hw⟩
  have hlog : logRadiusChart (slice (Real.log (y 0)) (angularProjection y)) = y :=
    (logRadiusChart_slice_exp _ _).trans (slice_exp_log_projection hr0)
  have hf := q.source_smooth i y hx
  have hp := q.positive_eventually i hx
  have hσ := (q.patch i).sigma_eventually (y := slice (Real.log (y 0)) (angularProjection y))
    (by simpa only [angularProjection_slice] using hw)
  obtain ⟨hm,h1,h2,h3,h4,hb⟩ := q.bounds i (angularProjection y) hw (Real.log (y 0))
  have hb' := hb (by rwa [Real.exp_log hr0])
  rw [hlog] at hb'
  have h := hcomp R (q.patch i).fields (Real.log (y 0)) (angularProjection y) hR1
    (by rwa [Real.exp_log hr0]) (by rwa [Real.exp_log hr0])
    (by rwa [hlog]) (by rwa [hlog]) hσ hm h1 h2 h3 h4 (by rwa [hlog]) v
  simpa only [hlog,slice_exp_log_projection hr0] using h
lemma polarLift_quadratic (P : SmoothAngularPatch) (F : CKSMixedGeometry.Point → AmbientMat)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) (v : E) :
    polarLift P F (polarParam P y) v v = quadratic3 (F y) (fderiv ℝ (polarInverse P) (polarParam P y) v) := by
  unfold polarLift
  rw [polarInverse_param P hr hy]
  change CKSTangentCoefficients.matrixBilinear (F y)
    (fderiv ℝ (polarInverse P) (polarParam P y) v)
    (fderiv ℝ (polarInverse P) (polarParam P y) v) = _
  exact CKSTangentCoefficients.matrixBilinear_apply _ _ _

end
end CKSLorentz

end





end OAI
end

section
namespace OAI




























































noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSAngularGeometry
open scoped ContDiff Matrix.Norms.Elementwise
lemma metricBlock_smoothAt {a : Point → ℝ} {b : Point → CKSAngularGeometry.Point}
    {q : Point → Mat} {x : Point}
    (ha : ContDiffAt ℝ ∞ a x) (hb : ContDiffAt ℝ ∞ b x) (hq : ContDiffAt ℝ ∞ q x) :
    ContDiffAt ℝ ∞ (fun y => metricBlock (a y) (b y) (q y)) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  refine Fin.cases ?_ (fun c => ?_) i
  · refine Fin.cases ?_ (fun d => ?_) j
    · exact ha
    · fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
  · refine Fin.cases ?_ (fun d => ?_) j
    · fin_cases c <;> simpa [metricBlock] using contDiffAt_pi.mp hb _
    · fin_cases c <;> fin_cases d <;> simpa [metricBlock] using contDiffAt_pi.mp (contDiffAt_pi.mp hq _) _
lemma sourceMetric_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceMetric f.base) y :=
  metricBlock_smoothAt (sourceRadialMetric_smoothAt hf.base hy) hf.base.b (sourceGamma_smoothAt hf.base hy)
lemma sourceTensor_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceTensor f) y :=
  metricBlock_smoothAt (sourceRadialK_smoothAt hf) hf.kb (sourceTangentialK_smoothAt hf.base hy)
end
end CKSMixedGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_spatial_regular {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v)
    {x : E} (hx : q.radius < ‖x‖) :
    ContDiffAt ℝ ∞ (sourceSpatial A) x ∧ ContDiffAt ℝ ∞ (sourceSpatial B) x ∧
    (∀ v w, sourceSpatial A x v w = sourceSpatial A x w v) ∧
    (∀ v : E, v ≠ 0 → 0 < sourceSpatial A x v v) ∧
    ∀ v w, sourceSpatial B x v w = sourceSpatial B x w v := by
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (q.radius_pos.trans hx),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rwa [hyr],hyw⟩
  have hs := q.source_smooth i y hy
  have hgp := polarLift_smooth_positive (q.patch i).patch (sourceMetric (q.patch i).fields.base)
    hy0 hyt (sourceMetric_smoothAt hs hy0.ne') (q.source_positive i y hy)
  have hkt := polarLift_smoothAt (q.patch i).patch (sourceTensor (q.patch i).fields)
    hy0 hyt (sourceTensor_smoothAt hs hy0.ne')
  have hks := polarLift_symmetric (q.patch i).patch (sourceTensor (q.patch i).fields)
    hy0 hyt (metricBlock_hermitian _ _ (q.source_symmetric i y hy))
  rw [hyx] at hgp hkt hks
  have he : ∀ᶠ z in 𝓝 x,
      sourceSpatial A z = polarLift (q.patch i).patch (sourceMetric (q.patch i).fields.base) z ∧
      sourceSpatial B z = polarLift (q.patch i).patch (sourceTensor (q.patch i).fields) z := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx,
      (polarCone_open _ (q.patch i).region_open).mem_nhds hc] with z hz hzc
    obtain ⟨hu,huw,hut,huz⟩ := polarCone_inverse (q.patch i).patch hzc
    have hr := spatial_source_reconstruction (q.patch i) hu hut
      (by rw [huz]; exact hA z hz) (by rw [huz]; exact hB z hz)
    rw [huz] at hr
    exact ⟨hr.2.2.1.symm,hr.2.2.2.symm⟩
  refine ⟨hgp.1.congr_of_eventuallyEq (he.mono (fun z hz => hz.1)),
    hkt.congr_of_eventuallyEq (he.mono (fun z hz => hz.2)),?_,?_,?_⟩
  · rw [he.self_of_nhds.1]; exact hgp.2.1
  · rw [he.self_of_nhds.1]; exact hgp.2.2
  · rw [he.self_of_nhds.2]; exact hks
end
end CKSLorentz

end








































noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma SourceCollarAtlas.eventually_closed_collar_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ l : ℝ → ℝ, Tendsto l atTop (𝓝 1) ∧
      (∀ R ≥ R₀, 0 ≤ l R ∧ l R ≤ 1) ∧
      ∀ R ≥ R₀, ∀ x : E, R ≤ ‖x‖ → ‖x‖ ≤ 3*R → ∀ v : E,
        l R * sourceSpatial A x v v ≤ q.metric R x v v := by
  obtain ⟨R₁,hR₁,hq₁,l,hl,hlb,hcomp⟩ := q.eventually_local_lower
  obtain ⟨R₂,hR₂,hq₂,hreg⟩ := q.eventually_pointwise
  refine ⟨max R₁ R₂,hR₁.trans (le_max_left _ _),hq₁.trans_le (le_max_left _ _),l,hl,?_,?_⟩
  · intro R hR; exact hlb R ((le_max_left _ _).trans hR)
  intro R hR x hr ht v
  have hR1 := (le_max_left R₁ R₂).trans hR
  have hR2 := (le_max_right R₁ R₂).trans hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hR₁.trans hR1)
  have hqx : q.radius < ‖x‖ := (hq₁.trans_le hR1).trans_le hr
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (hRpos.trans_le hr),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  have hyr : (polarInverse (q.patch i).patch x) 0 = ‖x‖ := by simp [polarInverse]
  let y := polarInverse (q.patch i).patch x
  have hrec := spatial_source_reconstruction (q.patch i) hy hyt
    (by rw [hyx]; exact hA x hqx) (by rw [hyx]; exact hB x hqx)
  have hg := (q.local_eq hRpos (hq₂.trans_le hR2)
    (fun i y hr ht hw => (hreg R hR2 i y hr ht hw).1) hr ht hc).1
  have hlower := hcomp R hR1 i y (by dsimp [y]; rw [hyr]; exact hr)
    (by dsimp [y]; rw [hyr]; exact ht) hyw (fderiv ℝ (polarInverse (q.patch i).patch) x v)
  rw [hg,← hyx,← hrec.2.2.1,polarLift_quadratic _ _ hy hyt]
  change _ ≤ polarLift (q.patch i).patch _ (polarParam (q.patch i).patch y) v v
  rw [polarLift_quadratic _ _ hy hyt]
  simpa only [hyx] using hlower
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSSphericalHarmonics Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem actual_same_end_uniform_lower {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ q.radius < R₀ ∧ ∃ ε : ℝ → ℝ,
      Tendsto ε atTop (𝓝 0) ∧ (∀ R ≥ R₀, 0 ≤ ε R ∧ ε R < 1) ∧
      ∀ R ≥ R₀, ∀ x : E, q.radius < ‖x‖ → ∀ v : E,
        (1-ε R)*sourceSpatial A x v v ≤ q.replacementMetric f₀ m R x v v := by
  obtain ⟨R₁,hR₁,hq₁,l₁,hl₁,hb₁,hc⟩ := q.eventually_closed_collar_lower hA hB
  obtain ⟨R₂,hR₂,hq₂,l₂,hl₂,hb₂,ho⟩ := q.eventually_outer_spatial_lower f₀ hf₀ m hA hB
  let l := fun R => min (l₁ R) (l₂ R)
  have hl : Tendsto l atTop (𝓝 1) := by simpa [l] using hl₁.min hl₂
  obtain ⟨R₃,h₃⟩ := eventually_atTop.mp (hl.eventually (Ioi_mem_nhds (zero_lt_one : (0:ℝ)<1)))
  let R₀ := max (max R₁ R₂) R₃
  have h01 : R₁ ≤ R₀ := (le_max_left R₁ R₂).trans (le_max_left _ _)
  have h02 : R₂ ≤ R₀ := (le_max_right R₁ R₂).trans (le_max_left _ _)
  have h03 : R₃ ≤ R₀ := le_max_right _ _
  refine ⟨R₀,hR₂.trans h02,hq₂.trans_le h02,fun R => 1-l R,?_,?_,?_⟩
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hl
  · intro R hR
    have ht : l R ≤ 1 := (min_le_left _ _).trans (hb₁ R (h01.trans hR)).2
    have hp := h₃ R (h03.trans hR)
    exact ⟨sub_nonneg.mpr ht,by linarith⟩
  intro R hR x hx v
  have hg : 0 ≤ sourceSpatial A x v v := by
    by_cases hv : v=0
    · simp [hv]
    · exact (q.source_spatial_regular hA hB hx).2.2.2.1 v hv |>.le
  have hl1 : l R ≤ l₁ R := min_le_left _ _
  have hl2 : l R ≤ l₂ R := min_le_right _ _
  simp only [sub_sub_cancel]
  unfold SourceCollarAtlas.replacementMetric
  split_ifs with hr ht
  · exact (mul_le_mul_of_nonneg_right
      (hl1.trans (hb₁ R (h01.trans hR)).2) hg).trans_eq (one_mul _)
  · exact (mul_le_mul_of_nonneg_right hl1 hg).trans
      (hc R (h01.trans hR) x (le_of_not_ge hr) ht v)
  · exact (mul_le_mul_of_nonneg_right hl2 hg).trans
      (ho R (h02.trans hR) x (le_of_not_ge ht) v)
end
end CKSLorentz

end























end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.actual_same_end_uniform_lower.{u_1} := @OAI.CKSLorentz.actual_same_end_uniform_lower.{u_1}
