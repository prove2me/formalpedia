-- Prove2me | solution 1 for OAI.CKSLorentz.actual_same_end_DEC
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:01:22.2261+00:00
-- url     : https://prove2.me/submissions/04cf3896-c0e8-457c-9060-daadd42a163f

import Mathlib
import Definitions.Def_CKSBondiPenrose
import Definitions.Def_CKSEndReplacementSupport
import Theorems.Thm_OAI_CKSCartesianOuter_constructed_cartesian_outer_DEC
import Theorems.Thm_OAI_CKSLorentz_SourceCollarAtlas_replacement_localization

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

lemma D_congr {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (e : E) : D e f x = D e g x := by
  unfold D
  rw [h.fderiv_eq]

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

lemma D_D {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (e w : E) :
    D w (D e f) x = fderiv ℝ (fderiv ℝ f) x w e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold D
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  simp

lemma D_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (e w : E) :
    D w (D e f) x = D e (D w f) x := by
  rw [D_D hf, D_D hf]
  exact hf.isSymmSndFDerivAt (by simp) w e

lemma diffAt_div {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (h0 : g x ≠ 0) :
    DifferentiableAt ℝ (fun y => f y / g y) x := by
  have hgi : DifferentiableAt ℝ (fun y => (g y)⁻¹) x := hg.inv h0
  simpa only [div_eq_mul_inv] using
    (show DifferentiableAt ℝ (fun y => f y * (g y)⁻¹) x from hf.fun_mul hgi)

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
namespace CKSFrame
noncomputable section
open scoped BigOperators
abbrev Coefficients := I → I → I → ℝ

def koszul (b : Coefficients) (i j k : I) : ℝ :=
  (b i j k-b j k i+b k i j)/2

end
end CKSFrame

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

lemma inverse_quadratic (q : Mat) (hq : determinant q ≠ 0) (b : Point) :
    (∑ i, ∑ k, q i k*(∑ a, inverse q i a*b a)*(∑ a, inverse q k a*b a)) =
      ∑ i, ∑ k, inverse q i k*(b i*b k) := by
  simp only [Fin.sum_univ_two,inverse]
  field_simp
  dsimp [determinant] at *
  ring

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

lemma foliationMetric_quadratic (U : ℝ) {γ : Mat} (hγ : γ.IsHermitian) (s : Point)
    (v : Fin 3 → ℝ) :
    star v ⬝ᵥ (foliationMetric U γ s *ᵥ v) =
      (v 0/U)^2+star (fun a : Fin 2 => v a.succ+s a*v 0) ⬝ᵥ
        (γ *ᵥ (fun a : Fin 2 => v a.succ+s a*v 0)) := by
  simp only [foliationMetric,metricBlock,Matrix.of_apply,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,star_trivial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,
    Matrix.tail_cons]
  simp only [Fin.succ_zero_eq_one',Fin.succ_one_eq_two']
  rw [hermitian_real_symmetry hγ 0 1]
  ring

theorem foliationMetric_posDef {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef) (s : Point) :
    (foliationMetric U γ s).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (metricBlock_hermitian _ _ hγ.isHermitian)
  intro v hv
  change 0 < star v ⬝ᵥ (foliationMetric U γ s *ᵥ v)
  rw [foliationMetric_quadratic U hγ.isHermitian s v]
  let y : Point := fun a => v a.succ+s a*v 0
  have hy0 := hγ.posSemidef.dotProduct_mulVec_nonneg y
  by_cases h0 : v 0=0
  · have hy : y ≠ 0 := by
      intro hy
      apply hv
      ext i
      fin_cases i
      · exact h0
      · have hh := congrFun hy 0; simpa [y,h0] using hh
      · have hh := congrFun hy 1; simpa [y,h0] using hh
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (hγ.dotProduct_mulVec_pos hy)
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (div_ne_zero h0 hU)) hy0

lemma foliationNormal_unit {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian) (s : Point) :
    star (foliationNormal U s) ⬝ᵥ (foliationMetric U γ s *ᵥ foliationNormal U s)=1 := by
  rw [foliationMetric_quadratic U hγ s]
  have hy : (fun a : Fin 2 => foliationNormal U s a.succ+s a*foliationNormal U s 0)=0 := by
    ext a; fin_cases a <;> simp [foliationNormal,mul_comm]
  rw [hy]
  simp [foliationNormal,hU]

lemma foliationNormal_orthogonal {U : ℝ} (_hU : U ≠ 0) {γ : Mat} (_hγ : γ.IsHermitian)
    (s : Point) (a : Fin 2) :
    ∑ j : Fin 3, foliationMetric U γ s a.succ j*foliationNormal U s j=0 := by
  fin_cases a <;> norm_num [Fin.succ,Fin.sum_univ_three,foliationMetric,metricBlock,Matrix.of_apply,foliationNormal,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.head_fin_const,Matrix.tail_cons,Matrix.cons_val_fin_one] <;> ring

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
open scoped BigOperators Topology

lemma christoffel_lowered {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : (G x).PosDef) (i j k : Fin 3) :
    (∑ l, coordinateChristoffel G x i j l * G x l k) =
      lowerKoszul (actualMetricFirstJet G x) i j k := by
  simp only [coordinateChristoffel, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hi := Matrix.nonsing_inv_mul (G x) (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  change (∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * ((G x)⁻¹ * G x) l k) = _
  rw [hi]
  change (∑ l, lowerKoszul (actualMetricFirstJet G x) i j l * (if l=k then 1 else 0)) = _
  simp

lemma actualMetricFirstJet_symmetric {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    actualMetricFirstJet G x i j k = actualMetricFirstJet G x i k j := by
  apply D_congr
  filter_upwards [hG] with y hy
  exact (hermitian_real_symmetry hy j k).symm

lemma coordinateChristoffel_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hG : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i j k : Fin 3) :
    coordinateChristoffel G x i j k = coordinateChristoffel G x j i k := by
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  unfold lowerKoszul
  rw [actualMetricFirstJet_symmetric hG l j i]
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
open scoped BigOperators Topology

lemma D_sum3 (e : PhysicalPoint) {x : PhysicalPoint} (f : Fin 3 → PhysicalPoint → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    D e (fun y => ∑ i, f i y) x = ∑ i, D e (f i) x := by
  simp only [D, fderiv_fun_sum (fun i _ => hf i), _root_.sum_apply]

lemma D_direction_expansion (e x : PhysicalPoint) (f : PhysicalPoint → ℝ) :
    D e f x = ∑ i, e i*D (CKSRealizedRound.basis i) f x := by
  unfold D
  conv_lhs => rw [direction_expansion e]
  simp

lemma D_metricPair (e : PhysicalPoint) {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : DifferentiableAt ℝ G x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    D e (fun y => metricPair (G y) (V y) (W y)) x =
      ∑ i, ∑ j, (D e (fun y => G y i j) x*V x i*W x j +
        G x i j*D e (fun y => V y i) x*W x j+
        G x i j*V x i*D e (fun y => W y j) x) := by
  have hgc (i j) : DifferentiableAt ℝ (fun y => G y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hg i) j
  have hvc (i) : DifferentiableAt ℝ (fun y => V y i) x := differentiableAt_pi.mp hv i
  have hwc (i) : DifferentiableAt ℝ (fun y => W y i) x := differentiableAt_pi.mp hw i
  have ht (i j) : DifferentiableAt ℝ (fun y => G y i j*V y i*W y j) x :=
    ((hgc i j).fun_mul (hvc i)).fun_mul (hwc j)
  have hsum (i) : DifferentiableAt ℝ (fun y => ∑ j, G y i j*V y i*W y j) x :=
    DifferentiableAt.fun_sum (fun j _ => ht i j)
  unfold metricPair
  rw [D_sum3 e _ hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [D_sum3 e _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [D_mul e ((hgc i j).fun_mul (hvc i)) (hwc j), D_mul e (hgc i j) (hvc i)]
  ring

lemma covariantVector_lowered {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : (G x).PosDef) (e : PhysicalPoint) (W : PhysicalPoint → PhysicalPoint) (k : Fin 3) :
    (∑ l, covariantVector G e W x l * G x l k) =
      (∑ l, D e (fun y => W y l) x * G x l k) +
      ∑ i, ∑ j, e i * W x j * lowerKoszul (actualMetricFirstJet G x) i j k := by
  simp only [covariantVector, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [christoffel_lowered hg]

lemma metricPair_symm {g : AmbientMat} (hg : g.IsHermitian) (v w : PhysicalPoint) :
    metricPair g v w=metricPair g w v := by
  unfold metricPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian_real_symmetry hg i j]
  ring

lemma metricPair_covariant {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : (G x).PosDef) (e w : PhysicalPoint) (V : PhysicalPoint → PhysicalPoint) :
    metricPair (G x) (covariantVector G e V x) w =
      (∑ k, (∑ l, D e (fun y => V y l) x * G x l k) * w k) +
      ∑ k, (∑ i, ∑ j, e i * V x j * lowerKoszul (actualMetricFirstJet G x) i j k) * w k := by
  unfold metricPair
  rw [Finset.sum_comm]
  simp_rw [mul_comm (G x _ _) (covariantVector G e V x _), ← Finset.sum_mul,
    covariantVector_lowered hg]
  simp [add_mul, Finset.sum_add_distrib]

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

lemma covariantVector_metric {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : DifferentiableAt ℝ G x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (e : PhysicalPoint) :
    D e (fun y => metricPair (G y) (V y) (W y)) x =
      metricPair (G x) (covariantVector G e V x) (W x) +
      metricPair (G x) (V x) (covariantVector G e W x) := by
  rw [D_metricPair e hg hv hw,
    metricPair_symm hp.isHermitian (V x) (covariantVector G e W x),
    metricPair_covariant hp, metricPair_covariant hp]
  have hd (i j) : D e (fun y => G y i j) x =
      ∑ a, e a * actualMetricFirstJet G x a i j := D_direction_expansion e x _
  simp_rw [hd]
  simp only [Fin.sum_univ_three, lowerKoszul]
  simp only [hermitian_real_symmetry hp.isHermitian 0 1,
    hermitian_real_symmetry hp.isHermitian 0 2,
    hermitian_real_symmetry hp.isHermitian 1 2,
    actualMetricFirstJet_symmetric hs 0 1 0,
    actualMetricFirstJet_symmetric hs 0 2 0,
    actualMetricFirstJet_symmetric hs 0 2 1,
    actualMetricFirstJet_symmetric hs 1 1 0,
    actualMetricFirstJet_symmetric hs 1 2 0,
    actualMetricFirstJet_symmetric hs 1 2 1,
    actualMetricFirstJet_symmetric hs 2 1 0,
    actualMetricFirstJet_symmetric hs 2 2 0,
    actualMetricFirstJet_symmetric hs 2 2 1]
  ring

lemma frameCoefficient_metric {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : DifferentiableAt ℝ G x)
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0)
    (i j k : Fin 3) : frameCoefficient G E x i j k = -frameCoefficient G E x i k j := by
  have h := covariantVector_metric hg (he j) (he k) hp hs (E i x)
  have hd : D (E i x) (fun y => metricPair (G y) (E j y) (E k y)) x=0 := by
    rw [D_congr (ho.mono (fun _ hy => hy j k)) (E i x)]
    exact D_const _ _ _
  rw [hd, metricPair_symm hp.isHermitian (E j x)] at h
  change 0=frameCoefficient G E x i j k+frameCoefficient G E x i k j at h
  linarith

lemma covariantVector_torsion {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (i j : Fin 3) :
    (fun k => covariantVector G (E i x) (E j) x k - covariantVector G (E j x) (E i) x k) =
      actualFrameBracket E x i j := by
  ext k
  have hsum : (∑ a, ∑ b, E i x a * E j x b * coordinateChristoffel G x a b k) =
      ∑ a, ∑ b, E j x a * E i x b * coordinateChristoffel G x a b k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [coordinateChristoffel_torsion hs b a]
    ring
  dsimp [covariantVector,actualFrameBracket]
  rw [hsum]
  ring

lemma frameCoefficient_torsion {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (i j k : Fin 3) :
    frameCoefficient G E x i j k-frameCoefficient G E x j i k=frameBracketCoefficient G E x i j k := by
  unfold frameBracketCoefficient
  rw [← covariantVector_torsion hs i j]
  simp only [frameCoefficient,metricPair,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem physical_frame_koszul {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : DifferentiableAt ℝ G x)
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) :
    frameCoefficient G E x = CKSFrame.koszul (frameBracketCoefficient G E x) := by
  funext i j k
  have h1 := frameCoefficient_torsion (E := E) hs i j k
  have h2 := frameCoefficient_torsion (E := E) hs j k i
  have h3 := frameCoefficient_torsion (E := E) hs k i j
  have hm1 := frameCoefficient_metric hg he hp hs ho i k j
  have hm2 := frameCoefficient_metric hg he hp hs ho j i k
  have hm3 := frameCoefficient_metric hg he hp hs ho k j i
  unfold CKSFrame.koszul
  linarith

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma orthonormal_frame_inverse {g : AmbientMat} {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (g*(Matrix.transpose e))*e=1 := by
  have hh : e*(g*Matrix.transpose e)=1 := by
    ext i j
    change (∑ k, e i k * ∑ l, g k l*e j l) = if i=j then 1 else 0
    rw [← ho i j]
    simp only [metricPair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  exact mul_eq_one_comm.mp hh

lemma orthonormal_frame_expansion {g : AmbientMat} {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v : PhysicalPoint) (j : Fin 3) :
    ∑ a, metricPair g v (e a)*e a j=v j := by
  have hm := orthonormal_frame_inverse ho
  calc
    _ = ∑ k, v k*((g*Matrix.transpose e)*e) k j := by
      simp only [metricPair, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ k, v k*(if k=j then 1 else 0) := by rw [hm]; rfl
    _ = v j := by simp

lemma metricPair_frame_left (k : AmbientMat) {g : AmbientMat}
    {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v w : PhysicalPoint) :
    ∑ a, metricPair g v (e a)*metricPair k (e a) w=metricPair k v w := by
  calc
    _ = ∑ i, ∑ j, k i j*(∑ a, metricPair g v (e a)*e a i)*w j := by
      simp only [metricPair, Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = metricPair k v w := by simp_rw [orthonormal_frame_expansion ho]; rfl

lemma metricPair_frame_right (k : AmbientMat) {g : AmbientMat}
    {e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0)
    (v w : PhysicalPoint) :
    ∑ a, metricPair g v (e a)*metricPair k w (e a)=metricPair k w v := by
  calc
    _ = ∑ i, ∑ j, k i j*w i*(∑ a, metricPair g v (e a)*e a j) := by
      simp only [metricPair, Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = metricPair k w v := by simp_rw [orthonormal_frame_expansion ho]; rfl

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
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff

lemma metricPair_foliationNormal {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) : metricPair (foliationMetric U γ s) (foliationNormal U s) (foliationNormal U s)=1 := by
  have h := foliationNormal_unit hU hγ s
  simpa only [metricPair,dotProduct,mulVec,star_apply,star_trivial,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc] using h

lemma metricPair_normal_tangent {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (v : PhysicalPoint) (hv : v 0=0) :
    metricPair (foliationMetric U γ s) v (foliationNormal U s)=0 := by
  unfold metricPair
  apply Finset.sum_eq_zero
  intro i _
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [hv]
  · calc
      _ = v a.succ * ∑ j, foliationMetric U γ s a.succ j * foliationNormal U s j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [foliationNormal_orthogonal hU hγ s a]; ring

lemma adaptedFrame_radial (U : ℝ) (γ : Mat) (s : Point) (a : Fin 2) :
    adaptedFrame U γ s a.succ 0=0 := by fin_cases a <;> rfl

lemma metricPair_tangent_expanded (U : ℝ) (γ : Mat) (s : Point)
    (v w : PhysicalPoint) (hv : v 0=0) (hw : w 0=0) :
    metricPair (foliationMetric U γ s) v w =
      γ 0 0*v 1*w 1+γ 0 1*v 1*w 2+(γ 1 0*v 2*w 1+γ 1 1*v 2*w 2) := by
  simp only [metricPair, Fin.sum_univ_three, hv, hw, mul_zero, zero_mul, zero_add, add_zero]
  rfl

lemma adaptedFrame_orthonormal {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.PosDef)
    (s : Point) (i j : Fin 3) :
    metricPair (foliationMetric U γ s) (adaptedFrame U γ s i) (adaptedFrame U γ s j)=
      if i=j then 1 else 0 := by
  have h00 : 0 < γ 0 0 := hγ.diag_pos
  have hd : 0 < γ.det := hγ.det_pos
  have ha : 0 < Real.sqrt (γ 0 0) := Real.sqrt_pos.mpr h00
  have hb : 0 < Real.sqrt γ.det := Real.sqrt_pos.mpr hd
  have ha2 := Real.sq_sqrt h00.le
  have hb2 := Real.sq_sqrt hd.le
  have hdet : γ.det=γ 0 0*γ 1 1-(γ 0 1)^2 := by
    rw [Matrix.det_fin_two,hermitian_real_symmetry hγ.isHermitian 0 1]
    ring
  have hn (a : Fin 2) := metricPair_normal_tangent hU hγ.isHermitian s
    (adaptedFrame U γ s a.succ) (adaptedFrame_radial U γ s a)
  have hgs : (foliationMetric U γ s).IsHermitian := metricBlock_hermitian _ _ hγ.isHermitian
  have hnt (a : Fin 2) : metricPair (foliationMetric U γ s) (adaptedFrame U γ s 0)
      (adaptedFrame U γ s a.succ)=0 := by
    rw [metricPair_symm hgs]
    exact hn a
  fin_cases i <;> fin_cases j
  · exact metricPair_foliationNormal hU hγ.isHermitian s
  · exact hnt 0
  · exact hnt 1
  · exact hn 0
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (Real.sqrt (γ 0 0))⁻¹ * (Real.sqrt (γ 0 0))⁻¹ +
      γ 0 1 * (Real.sqrt (γ 0 0))⁻¹ * 0 +
      (γ 1 0 * 0 * (Real.sqrt (γ 0 0))⁻¹ + γ 1 1 * 0 * 0) = 1
    simp only [mul_zero,zero_mul,add_zero]
    field_simp
    rw [ha2]
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (Real.sqrt (γ 0 0))⁻¹ * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
      γ 0 1 * (Real.sqrt (γ 0 0))⁻¹ * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) +
      (γ 1 0 * 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
       γ 1 1 * 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det)) = 0
    simp only [zero_mul,mul_zero,add_zero]
    field_simp
    rw [ha2]
    ring
  · exact hn 1
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (Real.sqrt (γ 0 0))⁻¹ +
      γ 0 1 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * 0 +
      (γ 1 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (Real.sqrt (γ 0 0))⁻¹ +
       γ 1 1 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * 0) = 0
    rw [hermitian_real_symmetry hγ.isHermitian 0 1]
    simp only [mul_zero,add_zero]
    field_simp
    rw [ha2]
    ring
  · rw [metricPair_tangent_expanded U γ s _ _ rfl rfl]
    change γ 0 0 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
      γ 0 1 * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) +
      (γ 1 0 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (-γ 0 1/(Real.sqrt (γ 0 0)*Real.sqrt γ.det)) +
       γ 1 1 * (Real.sqrt (γ 0 0)/Real.sqrt γ.det) * (Real.sqrt (γ 0 0)/Real.sqrt γ.det)) = 1
    rw [hermitian_real_symmetry hγ.isHermitian 0 1]
    field_simp
    rw [ha2,hb2,hdet]
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_det_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) : ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  simp only [Matrix.det_fin_three]
  fun_prop

lemma matrix_inv_component_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (G y)⁻¹ i j) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hd := (matrix_det_contDiffAt hg).inv h0
  simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 1 * G y 2 2 - G y 1 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 1 * G y 2 2) + G y 0 2 * G y 2 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 1 * G y 1 2 - G y 0 2 * G y 1 1)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 1 0 * G y 2 2) + G y 1 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 2 2 - G y 0 2 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 1 2) + G y 0 2 * G y 1 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 1 0 * G y 2 1 - G y 1 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (-(G y 0 0 * G y 2 1) + G y 0 1 * G y 2 0)) x
    exact hd.mul (by fun_prop)
  · change ContDiffAt ℝ ∞ (fun y => ((G y).det)⁻¹ * (G y 0 0 * G y 1 1 - G y 0 1 * G y 1 0)) x
    exact hd.mul (by fun_prop)

lemma coordinateChristoffel_contDiffAt {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => coordinateChristoffel G y i j k) x := by
  have hc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hdc (a i j) : ContDiffAt ℝ ∞
      (fun y => D (CKSRealizedRound.basis a) (fun z => G z i j) y) x :=
    contDiffAt_D (hc i j) (by simp) _
  have hi (i j) := matrix_inv_component_contDiffAt hg h0 i j
  unfold coordinateChristoffel
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul _ (hi l k)
  change ContDiffAt ℝ ∞ (fun y =>
    (D (CKSRealizedRound.basis i) (fun z => G z j l) y +
     D (CKSRealizedRound.basis j) (fun z => G z i l) y -
     D (CKSRealizedRound.basis l) (fun z => G z i j) y)/2) x
  exact (((hdc i j l).add (hdc j i l)).sub (hdc l i j)).div_const 2

lemma variable_direction_smooth {V : PhysicalPoint → PhysicalPoint}
    {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hv : ContDiffAt ℝ ∞ V x) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y => D (V y) f y) x := by
  exact (hf.fderiv_right (by simp)).clm_apply hv

lemma covariantVector_contDiffAt {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hv : ContDiffAt ℝ ∞ V x) (hw : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => covariantVector G (V y) W y) x := by
  have hvc i := contDiffAt_pi.mp hv i
  have hwc i := contDiffAt_pi.mp hw i
  apply contDiffAt_pi.mpr
  intro k
  have hd := variable_direction_smooth hv (hwc k)
  have hc (i j) := coordinateChristoffel_contDiffAt hg h0 i j k
  unfold covariantVector
  exact hd.add (ContDiffAt.sum (fun i _ => ContDiffAt.sum
    (fun j _ => ((hvc i).mul (hwc j)).mul (hc i j))))

lemma metricPair_contDiffAt {G : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hv : ContDiffAt ℝ ∞ V x)
    (hw : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => metricPair (G y) (V y) (W y)) x := by
  have hgc (i j) : ContDiffAt ℝ ∞ (fun y => G y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j
  have hvc i := contDiffAt_pi.mp hv i
  have hwc i := contDiffAt_pi.mp hw i
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum
    (fun j _ => ((hgc i j).mul (hvc i)).mul (hwc j)))

lemma frameCoefficient_contDiffAt {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (i j k : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => frameCoefficient G E y i j k) x :=
  metricPair_contDiffAt hg (covariantVector_contDiffAt hg h0 (he i) (he j)) (he k)

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology

 def ActualAdaptedAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame) (x : PhysicalPoint) : Prop :=
  DifferentiableAt ℝ G x ∧ (∀ i, DifferentiableAt ℝ (E i) x) ∧ (G x).PosDef ∧
  (∀ᶠ y in 𝓝 x, (G y).IsHermitian) ∧
  (∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0) ∧
  (∀ a b : Fin 2, frameBracketCoefficient G E x a.succ b.succ 0=0)

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

def frameTensor (K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : AmbientMat := fun i j => metricPair (K x) (E i x) (E j x)

def actualFrameTensorCovariant (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : ℝ :=
  D (E i x) (fun y => frameTensor K E y j k) x -
    ∑ a, (frameCoefficient G E x i j a*frameTensor K E x a k+
      frameCoefficient G E x i k a*frameTensor K E x j a)

def actualFrameMomentum (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (j : Fin 3) : ℝ :=
  (∑ i, actualFrameTensorCovariant G K E x i i j)-
    ∑ i, D (E j x) (fun y => frameTensor K E y i i) x

def actualFrameEnergy (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : ℝ :=
  (actualFrameScalar G E x+(∑ i, frameTensor K E x i i)^2-
    ∑ i, ∑ j, (frameTensor K E x i j)^2)/2

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
open Matrix Filter CKSCalculus
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationMetric_differentiableAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (h0 : U x ≠ 0) :
    DifferentiableAt ℝ (fun y => foliationMetric (U y) (γ y) (s y)) x := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have hrr : DifferentiableAt ℝ
      (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x :=
    (CKSCalculus.diffAt_div (differentiableAt_const 1) (hU.pow 2) (pow_ne_zero _ h0)).add
      (DifferentiableAt.fun_sum (fun a _ => DifferentiableAt.fun_sum
        (fun b _ => ((hγc a b).fun_mul (hsc a)).fun_mul (hsc b))))
  have hm (a) : DifferentiableAt ℝ (fun y => ∑ b, γ y a b*s y b) x :=
    DifferentiableAt.fun_sum (fun b _ => (hγc a b).fun_mul (hsc b))
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hγc 0 0
  · exact hγc 0 1
  · exact hm 1
  · exact hγc 1 0
  · exact hγc 1 1

lemma adaptedFrame_differentiableAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : DifferentiableAt ℝ U x) (hγ : DifferentiableAt ℝ γ x)
    (hs : DifferentiableAt ℝ s x) (hp : (γ x).PosDef) (i : Fin 3) :
    DifferentiableAt ℝ (fun y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have hγc (i j) : DifferentiableAt ℝ (fun y => γ y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hγ i) j
  have hsc (i) : DifferentiableAt ℝ (fun y => s y i) x := differentiableAt_pi.mp hs i
  have h00 : 0 < γ x 0 0 := hp.diag_pos
  have ha := (hγc 0 0).sqrt h00.ne'
  have hd : DifferentiableAt ℝ (fun y => (γ y).det) x := by
    simpa only [Matrix.det_fin_two] using
      ((hγc 0 0).fun_mul (hγc 1 1)).fun_sub ((hγc 0 1).fun_mul (hγc 1 0))
  have hb := hd.sqrt hp.det_pos.ne'
  have hapos := Real.sqrt_pos.mpr h00
  have hbpos := Real.sqrt_pos.mpr hp.det_pos
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hU
  · exact hU.neg.fun_mul (hsc 0)
  · exact hU.neg.fun_mul (hsc 1)
  · exact differentiableAt_const 0
  · exact ha.inv hapos.ne'
  · exact differentiableAt_const 0
  · exact differentiableAt_const 0
  · exact CKSCalculus.diffAt_div (hγc 0 1).neg (ha.fun_mul hb) (mul_ne_zero hapos.ne' hbpos.ne')
  · exact CKSCalculus.diffAt_div ha hb hbpos.ne'

lemma adaptedFrame_leafBracket {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : U x ≠ 0) (hγ : (γ x).IsHermitian) (a b : Fin 2) :
    frameBracketCoefficient (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x a.succ b.succ 0=0 := by
  apply metricPair_normal_tangent hU hγ
  change D _ (fun y => adaptedFrame (U y) (γ y) (s y) b.succ 0) x -
      D _ (fun y => adaptedFrame (U y) (γ y) (s y) a.succ 0) x = 0
  simp only [adaptedFrame_radial]
  have hz (e : PhysicalPoint) : D e (fun _ : PhysicalPoint => (0 : ℝ)) x=0 := by
    exact CKSCalculus.D_const e x 0
  rw [hz,hz]
  ring

theorem foliation_actualAdaptedAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    ∀ᶠ y in 𝓝 x, ActualAdaptedAt
      (fun z => foliationMetric (U z) (γ z) (s z))
      (fun i z => adaptedFrame (U z) (γ z) (s z) i) y := by
  have hu1 : ContDiffAt ℝ 1 U x := hU.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 γ x := hγ.of_le (by simp)
  have hs1 : ContDiffAt ℝ 1 s x := hs.of_le (by simp)
  have hu0 := hU.continuousAt.eventually_ne h0
  have hnear : ∀ᶠ y in 𝓝 x, U y ≠ 0 ∧ (γ y).PosDef := by
    filter_upwards [hu0,hp] with y hy hg
    exact ⟨hy,hg⟩
  filter_upwards [hu1.eventually (by norm_num), hg1.eventually (by norm_num),
    hs1.eventually (by norm_num),hnear,hnear.eventually_nhds] with y hyu hyg hys hyp hn
  refine ⟨foliationMetric_differentiableAt (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp.1,
    fun i => adaptedFrame_differentiableAt (hyu.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num)) (hys.differentiableAt (by norm_num)) hyp.2 i,
    foliationMetric_posDef hyp.1 hyp.2 (s y), ?_, ?_, ?_⟩
  · filter_upwards [hn] with z hz
    exact metricBlock_hermitian _ _ hz.2.isHermitian
  · filter_upwards [hn] with z hz
    exact adaptedFrame_orthonormal hz.1 hz.2 (s z)
  · exact adaptedFrame_leafBracket hyp.1 hyp.2.isHermitian

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_add_left (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g (v+w) z=metricPair g v z+metricPair g w z := by
  simp only [metricPair,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

lemma metricPair_add_right (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g v (w+z)=metricPair g v w+metricPair g v z := by
  simp only [metricPair,Pi.add_apply,mul_add,Finset.sum_add_distrib]

lemma D_metricPair_bilinear (e : PhysicalPoint) {K : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hk : DifferentiableAt ℝ K x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    D e (fun y => metricPair (K y) (V y) (W y)) x =
      metricPair (fun i j => D e (fun y => K y i j) x) (V x) (W x)+
      metricPair (K x) (fun i => D e (fun y => V y i) x) (W x)+
      metricPair (K x) (V x) (fun i => D e (fun y => W y i) x) := by
  rw [D_metricPair e hk hv hw]
  simp only [metricPair,Finset.sum_add_distrib]

lemma coordinateTensorCovariant_product_rule {G K : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hk : DifferentiableAt ℝ K x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) (e : PhysicalPoint) :
    coordinateTensorCovariant G K e (V x) (W x) x =
      D e (fun y => metricPair (K y) (V y) (W y)) x -
      metricPair (K x) (covariantVector G e V x) (W x) -
      metricPair (K x) (V x) (covariantVector G e W x) := by
  have hvv : covariantVector G e V x =
      (fun i => D e (fun y => V y i) x)+coordinateConnectionVector G e (V x) x := rfl
  have hww : covariantVector G e W x =
      (fun i => D e (fun y => W y i) x)+coordinateConnectionVector G e (W x) x := rfl
  rw [D_metricPair_bilinear e hk hv hw,hvv,hww,metricPair_add_left,metricPair_add_right]
  unfold coordinateTensorCovariant
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma orthonormal_frame_gram {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    e.transpose*e=g⁻¹ := by
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc]
  exact orthonormal_frame_inverse ho

lemma orthonormal_frame_completeness {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) (i j : Fin 3) :
    (∑ a, e a i*e a j)=g⁻¹ i j := by
  exact congrFun (congrFun (orthonormal_frame_gram ho) i) j

lemma frame_tensor_matrix (k e : AmbientMat) :
    Matrix.of (fun i j => metricPair k (e i) (e j))=e*k*e.transpose := by
  ext i j
  change (∑ a, ∑ b, k a b*e i a*e j b) = (∑ b, (∑ a, e i a*k a b)*e j b)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma frame_trace_exact (k : AmbientMat) {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ i, metricPair k (e i) (e i))=(g⁻¹*k).trace := by
  change (Matrix.of (fun i j => metricPair k (e i) (e j))).trace = _
  rw [frame_tensor_matrix,Matrix.trace_mul_comm,
    ← Matrix.mul_assoc e.transpose e,orthonormal_frame_gram ho]

lemma symmetric_square_trace {k : AmbientMat} (hk : k.IsHermitian) :
    (∑ i, ∑ j, (k i j)^2)=(k*k).trace := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hermitian_real_symmetry hk i j]
  ring

lemma frame_tensor_norm_exact {k g e : AmbientMat} (hk : k.IsHermitian)
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ i, ∑ j, (metricPair k (e i) (e j))^2)=(g⁻¹*k*g⁻¹*k).trace := by
  let t : AmbientMat := Matrix.of (fun i j => metricPair k (e i) (e j))
  have ht : t.IsHermitian := by
    ext i j
    change metricPair k (e j) (e i)=metricPair k (e i) (e j)
    exact metricPair_symm hk _ _
  change (∑ i, ∑ j, (t i j)^2)=_
  rw [symmetric_square_trace ht]
  have he : t=e*k*e.transpose := frame_tensor_matrix k e
  rw [he]
  calc
    _ = (e*(k*(e.transpose*e)*k*e.transpose)).trace := by congr 1; simp only [Matrix.mul_assoc]
    _ = ((k*(e.transpose*e)*k*e.transpose)*e).trace := Matrix.trace_mul_comm _ _
    _ = (k*(e.transpose*e)*k*(e.transpose*e)).trace := by congr 1; simp only [Matrix.mul_assoc]
    _ = (k*g⁻¹*k*g⁻¹).trace := by rw [orthonormal_frame_gram ho]
    _ = (g⁻¹*k*g⁻¹*k).trace := by
      rw [Matrix.trace_mul_comm (k*g⁻¹*k) g⁻¹]
      simp only [Matrix.mul_assoc]

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_differentiableAt {K : PhysicalPoint → AmbientMat}
    {V W : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint}
    (hk : DifferentiableAt ℝ K x) (hv : DifferentiableAt ℝ V x)
    (hw : DifferentiableAt ℝ W x) :
    DifferentiableAt ℝ (fun y => metricPair (K y) (V y) (W y)) x := by
  have hkc (i j) : DifferentiableAt ℝ (fun y => K y i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hk i) j
  have hvc i : DifferentiableAt ℝ (fun y => V y i) x := differentiableAt_pi.mp hv i
  have hwc i : DifferentiableAt ℝ (fun y => W y i) x := differentiableAt_pi.mp hw i
  exact DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum
    (fun j _ => ((hkc i j).fun_mul (hvc i)).fun_mul (hwc j)))

lemma coordinateTensorCovariant_bilinear (G K : PhysicalPoint → AmbientMat)
    (x e v w : PhysicalPoint) :
    coordinateTensorCovariant G K e v w x =
      metricPair (fun i j => coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x) e v := by
  have hb (a b) : coordinateTensorCovariant G K
      (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) w x =
      (∑ j, D (CKSRealizedRound.basis a) (fun y => K y b j) x*w j) -
      (∑ i, ∑ j, K x i j*coordinateChristoffel G x a b i*w j) -
      (∑ j, K x b j*(∑ c, w c*coordinateChristoffel G x a c j)) := by
    simp [coordinateTensorCovariant,coordinateConnectionVector,metricPair,
      CKSRealizedRound.basis,Pi.single_apply]
  have hd (i j) : D e (fun y => K y i j) x =
      ∑ a, e a*D (CKSRealizedRound.basis a) (fun y => K y i j) x :=
    D_direction_expansion e x _
  have h₁ : metricPair (fun i j => D e (fun y => K y i j) x) v w =
      ∑ a, ∑ b, (∑ j, D (CKSRealizedRound.basis a) (fun y => K y b j) x*w j)*e a*v b := by
    unfold metricPair
    simp only [hd,Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : metricPair (K x) (coordinateConnectionVector G e v x) w =
      ∑ a, ∑ b, (∑ i, ∑ j, K x i j*coordinateChristoffel G x a b i*w j)*e a*v b := by
    simp only [metricPair,coordinateConnectionVector,Finset.sum_mul,Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₃ : metricPair (K x) v (coordinateConnectionVector G e w x) =
      ∑ a, ∑ b, (∑ j, K x b j*(∑ c, w c*coordinateChristoffel G x a c j))*e a*v b := by
    simp only [metricPair,coordinateConnectionVector,Finset.sum_mul,Finset.mul_sum]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    ring
  unfold metricPair
  simp_rw [hb,sub_mul,Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) (congrArg₂ (· - ·) h₁ h₂) h₃

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma covector_frame_square (ρ : PhysicalPoint) {g e : AmbientMat}
    (ho : ∀ i j, metricPair g (e i) (e j)=if i=j then 1 else 0) :
    (∑ a, (∑ i, ρ i*e a i)^2)=metricPair g⁻¹ ρ ρ := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  unfold metricPair
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑ a, e a i*e a j)*ρ i*ρ j := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [orthonormal_frame_completeness ho]

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology Matrix.Norms.Elementwise

lemma metricPair_smul_left (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g (r • v) w=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma metricPair_smul_right (g : AmbientMat) (r : ℝ) (v w : PhysicalPoint) :
    metricPair g v (r • w)=r*metricPair g v w := by
  simp only [metricPair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coordinateConnectionVector_add_right (G : PhysicalPoint → AmbientMat)
    (x e v w : PhysicalPoint) :
    coordinateConnectionVector G e (v+w) x=
      coordinateConnectionVector G e v x+coordinateConnectionVector G e w x := by
  ext k
  simp only [coordinateConnectionVector,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

lemma coordinateConnectionVector_smul_right (G : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) (r : ℝ) :
    coordinateConnectionVector G e (r • v) x=r • coordinateConnectionVector G e v x := by
  ext k
  simp only [coordinateConnectionVector,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def coordinateTensorCovariantLast (G K : PhysicalPoint → AmbientMat)
    (x e v : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := fun w => coordinateTensorCovariant G K e v w x
  map_add' := by
    intro w z
    simp only [coordinateTensorCovariant,coordinateConnectionVector_add_right,
      metricPair_add_right]
    erw [metricPair_add_right]
    ring
  map_smul' := by
    intro r w
    simp only [coordinateTensorCovariant,coordinateConnectionVector_smul_right,
      metricPair_smul_right,smul_eq_mul,RingHom.id_apply]
    erw [metricPair_smul_right]
    ring

def coordinateMomentumLinear (G K : PhysicalPoint → AmbientMat)
    (x : PhysicalPoint) : PhysicalPoint →ₗ[ℝ] ℝ where
  toFun := coordinateMomentum G K x
  map_add' := by
    intro w z
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (w+z) x=
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x+
        coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) z x :=
      (coordinateTensorCovariantLast G K x _ _).map_add w z
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,mul_add,Finset.sum_add_distrib,D,map_add]
    ring
  map_smul' := by
    intro r w
    have hc (i j) : coordinateTensorCovariant G K
        (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) (r • w) x=
        r*coordinateTensorCovariant G K (CKSRealizedRound.basis i) (CKSRealizedRound.basis j) w x :=
      (coordinateTensorCovariantLast G K x _ _).map_smul r w
    simp only [coordinateMomentum,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.of_apply,hc,D,map_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_left_comm _ r,← Finset.mul_sum]
    ring

lemma coordinateMomentum_expansion (G K : PhysicalPoint → AmbientMat)
    (x w : PhysicalPoint) :
    coordinateMomentum G K x w=
      ∑ i, coordinateMomentum G K x (CKSRealizedRound.basis i)*w i := by
  change coordinateMomentumLinear G K x w=_
  conv_lhs => rw [direction_expansion w]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,coordinateMomentumLinear,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma covariant_second_pair {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0)
    (i j k l : Fin 3) :
    metricPair (G x)
      (covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x)
      (E l x) = D (E i x) (fun y => frameCoefficient G E y j k l) x +
      ∑ m, frameCoefficient G E x j k m*frameCoefficient G E x i m l := by
  have hh := covariantVector_metric (hg.differentiableAt (by simp))
    ((covariantVector_contDiffAt hg (ne_of_gt hp.det_pos) (he j) (he k)).differentiableAt (by simp))
    ((he l).differentiableAt (by simp)) hp hs (E i x)
  have hpairs := metricPair_frame_right (G x) ho.self_of_nhds
    (covariantVector G (E i x) (E l) x) (covariantVector G (E j x) (E k) x)
  change (∑ m, frameCoefficient G E x i l m*frameCoefficient G E x j k m) = _ at hpairs
  have hm (m) := frameCoefficient_metric (hg.differentiableAt (by simp))
    (fun a => (he a).differentiableAt (by simp)) hp hs ho i l m
  simp_rw [hm] at hpairs
  have hpairs' : metricPair (G x) (covariantVector G (E j x) (E k) x)
      (covariantVector G (E i x) (E l) x) =
      -(∑ m, frameCoefficient G E x j k m*frameCoefficient G E x i m l) := by
    rw [← hpairs]
    simp only [neg_mul,Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  change D (E i x) (fun y => frameCoefficient G E y j k l) x = _ at hh
  rw [hpairs'] at hh
  linarith

def covariantDirectionLinear (G : PhysicalPoint → AmbientMat)
    (W : PhysicalPoint → PhysicalPoint) (x : PhysicalPoint) :
    PhysicalPoint →ₗ[ℝ] PhysicalPoint where
  toFun e := covariantVector G e W x
  map_add' e f := by
    ext k
    simp only [covariantVector,D,map_add,Pi.add_apply,
      add_mul,Finset.sum_add_distrib]
    ring
  map_smul' r e := by
    ext k
    simp only [covariantVector,D,map_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma metricPair_sum_left (g : AmbientMat) (v : Fin 3 → PhysicalPoint) (w : PhysicalPoint) :
    metricPair g (∑ i, v i) w=∑ i, metricPair g (v i) w := by
  simp only [Fin.sum_univ_three,metricPair_add_left]

lemma covariant_frame_direction {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (ho : ∀ i j,
      metricPair (G x) (E i x) (E j x)=if i=j then 1 else 0)
    (e : PhysicalPoint) (j k : Fin 3) :
    metricPair (G x) (covariantVector G e (E j) x) (E k x)=
      ∑ m, metricPair (G x) e (E m x)*frameCoefficient G E x m j k := by
  have hex : e=∑ m, metricPair (G x) e (E m x) • E m x := by
    ext a
    simpa only [Fin.sum_univ_three,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
      (orthonormal_frame_expansion ho e a).symm
  change metricPair (G x) (covariantDirectionLinear G (E j) x e) (E k x)=_
  conv_lhs => rw [hex]
  rw [map_sum]
  simp only [map_smul,metricPair_sum_left,metricPair_smul_left]
  rfl

theorem actualFrameCurvature_operator {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0)
    (i j k l : Fin 3) :
    actualFrameCurvature G E x i j k l =
      metricPair (G x)
        (covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x) (E l x) -
      metricPair (G x)
        (covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x) (E l x) -
      metricPair (G x) (covariantVector G (actualFrameBracket E x i j) (E k) x) (E l x) := by
  rw [covariant_second_pair hg he hp hs ho,covariant_second_pair hg he hp hs ho,
    covariant_frame_direction ho.self_of_nhds]
  simp only [actualFrameCurvature,frameBracketCoefficient,Finset.sum_sub_distrib]
  ring

lemma metricPair_sub_left (g : AmbientMat) (v w z : PhysicalPoint) :
    metricPair g (v-w) z=metricPair g v z-metricPair g w z := by
  simp only [metricPair,Pi.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

def curvatureVector (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) (i j k : Fin 3) : PhysicalPoint :=
  covariantVector G (E i x) (fun y => covariantVector G (E j y) (E k) y) x -
  covariantVector G (E j x) (fun y => covariantVector G (E i y) (E k) y) x -
  covariantVector G (actualFrameBracket E x i j) (E k) x

theorem actualScalar_curvature_trace {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x =
      ∑ i, ∑ j, metricPair (G x) (curvatureVector G E x i j j) (E i x) := by
  simp only [actualFrameScalar,curvatureVector,metricPair_sub_left]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact actualFrameCurvature_operator hg he hp hs ho i j j i

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
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma foliationMetric_contDiffAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => foliationMetric (U y) (γ y) (s y)) x := by
  have hγc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have hrr : ContDiffAt ℝ ∞
      (fun y => 1/(U y)^2+∑ a, ∑ b, γ y a b*s y a*s y b) x :=
    (contDiffAt_const.div (hU.pow 2) (pow_ne_zero _ h0)).add
      (ContDiffAt.sum (fun a _ => ContDiffAt.sum
        (fun b _ => ((hγc a b).mul (hsc a)).mul (hsc b))))
  have hm (a) : ContDiffAt ℝ ∞ (fun y => ∑ b, γ y a b*s y b) x :=
    ContDiffAt.sum (fun b _ => (hγc a b).mul (hsc b))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hrr
  · exact hm 0
  · exact hm 1
  · exact hm 0
  · exact hγc 0 0
  · exact hγc 0 1
  · exact hm 1
  · exact hγc 1 0
  · exact hγc 1 1

lemma adaptedFrame_contDiffAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (hp : (γ x).PosDef) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have hγc (i j) : ContDiffAt ℝ ∞ (fun y => γ y i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hγ i) j
  have hsc (i) : ContDiffAt ℝ ∞ (fun y => s y i) x := contDiffAt_pi.mp hs i
  have h00 : 0 < γ x 0 0 := hp.diag_pos
  have ha := (hγc 0 0).sqrt h00.ne'
  have hd : ContDiffAt ℝ ∞ (fun y => (γ y).det) x := by
    simpa only [Matrix.det_fin_two] using
      ((hγc 0 0).mul (hγc 1 1)).sub ((hγc 0 1).mul (hγc 1 0))
  have hb := hd.sqrt hp.det_pos.ne'
  have hapos := Real.sqrt_pos.mpr h00
  have hbpos := Real.sqrt_pos.mpr hp.det_pos
  apply contDiffAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact hU
  · exact hU.neg.mul (hsc 0)
  · exact hU.neg.mul (hsc 1)
  · exact contDiffAt_const
  · exact ha.inv hapos.ne'
  · exact contDiffAt_const
  · exact contDiffAt_const
  · exact (hγc 0 1).neg.div (ha.mul hb) (mul_ne_zero hapos.ne' hbpos.ne')
  · exact ha.div hb hbpos.ne'

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
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma primitive_hasDerivAt {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : HasDerivAt (primitive a q) (q r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (positive_interval_integrable hq ha hr)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hq r hr)
    (hq.continuousAt (isOpen_Ioi.mem_nhds hr))

lemma primitive_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {a : ℝ} (ha : 0 < a) : ContDiffOn ℝ ∞ (primitive a q) (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  constructor
  · intro r hr
    exact (primitive_hasDerivAt hq.continuousOn ha hr).differentiableAt.differentiableWithinAt
  · exact hq.congr (fun r hr => (primitive_hasDerivAt hq.continuousOn ha hr).deriv)

lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))

end
end CKSBending

end

end OAI
end

section
namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

lemma paddingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (paddingWeight R) := by
  unfold paddingWeight
  fun_prop

lemma paddingIntegrand_smooth (R : ℝ) :
    ContDiffOn ℝ ∞ (fun r => paddingWeight R r * paddingDensity r) (Ioi 0) :=
  (paddingWeight_smooth R).contDiffOn.mul paddingDensity_smooth
lemma paddingMass_smooth {R : ℝ} (hR : 0 < R) : ContDiffOn ℝ ∞ (paddingMass R) (Ioi 0) :=
  primitive_smooth (paddingIntegrand_smooth R) hR

end
end CKSBending

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
open CKSCalculus Set Filter
open scoped BigOperators Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma physical_D_div_const (e : PhysicalPoint) {f : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    D e (fun y => f y/c) x = D e f x/c := by
  simp only [div_eq_mul_inv]
  rw [D_mul e hf (differentiableAt_const _),D_const]
  ring

end
end CKSAngularGeometry

end






















noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

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

lemma collarT_smoothAt (R : ℝ) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarT R f) y :=
  contDiffAt_const.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.tError)

lemma collarF_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {y : MP} (hf : f.SmoothAt y) :
    ContDiffAt ℝ ∞ (collarF R f) y :=
  (hf.fstar.add ((contDiffAt_const.sub (collarWeight_smoothAt R y)).mul hf.massError)).add
    (radialLift_smoothAt ((paddingMass_smooth hR).contDiffAt
      (isOpen_Ioi.mem_nhds (Real.exp_pos (y 0)))))

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

lemma physicalCollarT_smoothAt (R : ℝ) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarT R f) x :=
  (collarT_smoothAt R hf).comp x (radiusLogPoint_smoothAt hr)

lemma physicalCollarF_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x)) :
    ContDiffAt ℝ ∞ (physicalCollarF R f) x :=
  (collarF_smoothAt hR hf).comp x (radiusLogPoint_smoothAt hr)

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

lemma radialMassRadical_smoothAt {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x) (hr : x 0 ≠ 0) :
    ContDiffAt ℝ ∞ (radialMassRadical t F) x := by
  have hrad : ContDiffAt ℝ ∞ (fun y : PhysicalPoint => y 0) x := by fun_prop
  exact (contDiffAt_const.add ((hrad.mul ht).pow 2)).sub
    ((contDiffAt_const.mul hF).div hrad hr)

lemma radialMassLapse_smoothAt {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint}
    (hγ : ContDiffAt ℝ ∞ γ x) (hs : ContDiffAt ℝ ∞ s x)
    (ht : ContDiffAt ℝ ∞ t x) (hF : ContDiffAt ℝ ∞ F x)
    (hr : x 0 ≠ 0) (hp : (γ x).PosDef)
    (hd : radialExpansion γ s x ≠ 0) (hu : radialMassRadical t F x ≠ 0) :
    ContDiffAt ℝ ∞ (radialMassLapse γ s t F) x :=
  ((radialMassRadical_smoothAt ht hF hr).sqrt hu).div
    (radialExpansion_smoothAt hγ hs hp) hd

end
end CKSAngularGeometry

end








noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalCollarU_smoothAt {R : ℝ} (hR : 0 < R) {f : LogCollarData} {x : PhysicalPoint}
    (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hp : (physicalCollarGamma R f x).PosDef)
    (hd : radialExpansion (physicalCollarGamma R f) (physicalCollarShift R f) x ≠ 0)
    (hu : radialMassRadical (physicalCollarT R f) (physicalCollarF R f) x ≠ 0) :
    ContDiffAt ℝ ∞ (physicalCollarU R f) x :=
  radialMassLapse_smoothAt (physicalCollarGamma_smoothAt R hr hf)
    (physicalCollarShift_smoothAt R hr hf) (physicalCollarT_smoothAt R hr hf)
    (physicalCollarF_smoothAt hR hr hf) hr hp hd hu

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

lemma sourceLapse_pos {f : SourceMassFields} {x : Point} (hp : (sourceMetric f x).PosDef) :
    0 < sourceLapse f x := one_div_pos.mpr (Real.sqrt_pos.mpr (metricBlock_schur_positive hp))

lemma source_metric_foliation {f : SourceMassFields} {x : Point} (hp : (sourceMetric f x).PosDef) :
    foliationMetric (sourceLapse f x) (sourceGamma f x) (sourceShift f x)=sourceMetric f x := by
  have hq : determinant (sourceGamma f x) ≠ 0 := by
    rw [determinant_eq]
    exact (metricBlock_leaf_posDef hp).det_pos.ne'
  have hs : 0 < sourceSchur f x := metricBlock_schur_positive hp
  have hr : 1/(sourceLapse f x)^2=sourceSchur f x := by
    rw [sourceLapse,div_pow,one_pow,Real.sq_sqrt hs.le]
    field_simp
  unfold foliationMetric sourceMetric
  rw [hr]
  have hv : (fun a => ∑ b, sourceGamma f x a b*sourceShift f x b)=f.b x := by
    funext a
    exact inverse_mul_vector (sourceGamma f x) hq (f.b x) a
  rw [hv]
  congr 1
  unfold sourceSchur sourceShift
  rw [inverse_quadratic _ hq]
  ring

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
open Matrix CKSCalculus Filter CKSAngularGeometry CKSAngularSlice CKSBending
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma SourceMassFields.SmoothAt.regularAt {f : SourceMassFields} {x : Point}
    (hf : f.SmoothAt x) : f.RegularAt x := by
  exact ⟨hf.sigma.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.mK.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),
    hf.mr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.eg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.ek.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.b.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _),hf.err.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)⟩

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




end OAI
end

section
namespace OAI

noncomputable section
namespace CKSLorentz
noncomputable section
open scoped ContDiff Manifold Topology
open MeasureTheory
open CKSSphericalHarmonics (SmoothSphere surfaceMeasure Balanced sphereIntegral sphereArea)

lemma heatDatum_smooth {M : Sphere → ℝ} (hM : SmoothSphere M) :
    SmoothSphere (heatDatum M hM) := hM.div_const 4

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

lemma sourceCollar_symmetries {f : SourceTensorFields} {x : Point}
    (hp : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceMetric f.base y).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (f.base.sigma (angularProjection y)).IsHermitian)
    (hk : ∀ᶠ y in 𝓝 (logRadiusChart x), (sourceTangentialK f.base y).IsHermitian) :
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).sigma y).IsHermitian) ∧
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).metricError y).IsHermitian) ∧
    (∀ᶠ y in 𝓝 x, ((sourceCollarData f.logFields).tauDivR2 y).IsHermitian) := by
  have hc := logRadiusChart_smooth.continuous.continuousAt (x:=x)
  have hp' := hc.tendsto.eventually hp
  have hk' := hc.tendsto.eventually hk
  refine ⟨hs,?_,?_⟩
  · filter_upwards [hp',hs] with y hyp hys
    exact sourceCollar_metricError_hermitian hyp hys
  · filter_upwards [hp',hk'] with y hyp hyk
    exact sourceCollar_tau_hermitian hyp hyk

end
end CKSMixedGeometry

end












noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology
lemma spatialDirection_val {x : E} (hx : x ≠ 0) : (spatialDirection x : E) = normalizeAmbient x := by
  simp [spatialDirection,hx]

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
lemma SourceCollarAtlas.symmetric_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    ∀ᶠ z in 𝓝 y, (sourceTangentialK (q.patch i).fields.base z).IsHermitian := by
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy] with z hz
  exact q.source_symmetric i z hz

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






end OAI
end

section
namespace OAI




noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma actual_inverse_derivative {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (v : PhysicalPoint) :
    (fun i j => D v (fun y => (G y)⁻¹ i j) x) =
      -(G x)⁻¹ * (show AmbientMat from fun i j => D v (fun y => G y i j) x) * (G x)⁻¹ := by
  let dG : AmbientMat := fun i j => D v (fun y => G y i j) x
  let dI : AmbientMat := fun i j => D v (fun y => (G y)⁻¹ i j) x
  have hc (i j) : DifferentiableAt ℝ (fun y => G y i j) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j).differentiableAt (by simp)
  have hi (i j) : DifferentiableAt ℝ (fun y => (G y)⁻¹ i j) x :=
    (matrix_inv_component_contDiffAt hg h0 i j).differentiableAt (by simp)
  have hz : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    (matrix_det_contDiffAt hg).continuousAt.eventually_ne h0
  have hD : dG * (G x)⁻¹ + G x * dI = 0 := by
    ext i j
    have hd : D v (fun y => (G y * (G y)⁻¹) i j) x = 0 := by
      calc
        _ = D v (fun _ => (1 : AmbientMat) i j) x := by
          apply D_congr
          filter_upwards [hz] with y hy
          rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy)]
        _ = 0 := D_const _ _ _
    simp only [Matrix.mul_apply] at hd
    rw [D_sum3 v (fun k y => G y i k * (G y)⁻¹ k j)
      (fun k => (hc i k).fun_mul (hi k j))] at hd
    simp only [D_mul _ (hc i _) (hi _ j)] at hd
    change (∑ k, dG i k * (G x)⁻¹ k j) + (∑ k, G x i k * dI k j) = 0
    simpa only [dG, dI, Finset.sum_add_distrib, add_comm, mul_comm] using hd
  have hIG : (G x)⁻¹ * G x = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h0)
  have hD' : G x * dI = -(dG * (G x)⁻¹) := (eq_neg_iff_add_eq_zero).2 (by
    simpa only [add_comm] using hD)
  change dI = -(G x)⁻¹ * dG * (G x)⁻¹
  calc
    dI = ((G x)⁻¹ * G x) * dI := by rw [hIG, one_mul]
    _ = (G x)⁻¹ * (G x * dI) := mul_assoc _ _ _
    _ = -(G x)⁻¹ * dG * (G x)⁻¹ := by rw [hD']; simp only [mul_neg, neg_mul, mul_assoc]

lemma physicalMetricJet_dInv {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) (a i j : Fin 3) :
    D (CKSRealizedRound.basis a) (fun y => (G y)⁻¹ i j) x =
      (physicalMetricJet G x).dInv a i j := by
  have h := congrFun (congrFun (actual_inverse_derivative hg h0
    (CKSRealizedRound.basis a)) i) j
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_apply] at h
  change D (CKSRealizedRound.basis a) (fun y => (G y)⁻¹ i j) x =
    -(∑ c, (∑ b, (G x)⁻¹ i b * D (CKSRealizedRound.basis a)
      (fun y => G y b c) x) * (G x)⁻¹ c j) at h
  rw [h]
  simp only [CKSRound.MetricJet.dInv, physicalMetricJet, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_gamma {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) (a i j : Fin 3) :
    (physicalMetricJet G x).gamma a i j = coordinateChristoffel G x i j a := by
  simp only [CKSRound.MetricJet.gamma, physicalMetricJet, coordinateChristoffel,
    lowerKoszul, actualMetricFirstJet, Finset.sum_div]
  apply Finset.sum_congr rfl; intro l _
  rw [hermitian_real_symmetry hs.inv a l]
  ring

lemma physicalMetricJet_dGamma {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (s a i j : Fin 3) :
    D (CKSRealizedRound.basis s) (fun y => coordinateChristoffel G y i j a) x =
      (physicalMetricJet G x).dGamma s a i j := by
  have hc (b c) : ContDiffAt ℝ ∞ (fun y => G y b c) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hg b) c
  have hd (b c d) : DifferentiableAt ℝ
      (fun y => D (CKSRealizedRound.basis b) (fun z => G z c d) y) x :=
    (contDiffAt_D (hc c d) (m := ∞) (by simp) _).differentiableAt (by simp)
  have hi (b c) : DifferentiableAt ℝ (fun y => (G y)⁻¹ b c) x :=
    (matrix_inv_component_contDiffAt hg h0 b c).differentiableAt (by simp)
  have ht (l) := ((hd i j l).fun_add (hd j i l)).fun_sub (hd l i j)
  have hm (l) := (hi a l).fun_mul (ht l)
  calc
    _ = D (CKSRealizedRound.basis s) (fun y => (physicalMetricJet G y).gamma a i j) x := by
      apply D_congr
      filter_upwards [hs] with y hy
      exact (physicalMetricJet_gamma hy a i j).symm
    _ = _ := by
      unfold CKSRound.MetricJet.gamma
      change D (CKSRealizedRound.basis s) (fun y =>
        (∑ l, (G y)⁻¹ a l * (D (CKSRealizedRound.basis i) (fun z => G z j l) y +
          D (CKSRealizedRound.basis j) (fun z => G z i l) y -
          D (CKSRealizedRound.basis l) (fun z => G z i j) y)) / 2) x = _
      rw [physical_D_div_const _ (DifferentiableAt.fun_sum (fun l _ => hm l)),
        D_sum3 _ _ hm]
      unfold CKSRound.MetricJet.dGamma
      congr 1
      apply Finset.sum_congr rfl; intro l _
      rw [D_mul _ (hi a l) (ht l), D_sub _ ((hd i j l).fun_add (hd j i l)) (hd l i j),
        D_add _ (hd i j l) (hd j i l), physicalMetricJet_dInv hg h0]
      simp only [physicalMetricJet]
      ring

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSCalculus CKSAngularGeometry Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

abbrev A := Fin 3
abbrev P := PhysicalPoint
abbrev Vect := PhysicalPoint
abbrev Symbols := A → A → A → ℝ

def delta (v : Vect) (f : P → ℝ) (x : P) : ℝ := D v f x

lemma delta_expansion (v : Vect) (f : P → ℝ) (x : P) :
    delta v f x = ∑ i : A, v i * D (CKSRealizedRound.basis i) f x :=
  D_direction_expansion v x f

lemma delta_mul (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y * g y) x = f x * delta v g x + g x * delta v f x :=
  D_mul _ hf hg

lemma delta_add (v : Vect) {f g : P → ℝ} {x : P}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    delta v (fun y => f y + g y) x = delta v f x + delta v g x :=
  D_add _ hf hg

lemma delta_sum (v : Vect) {x : P} (f : A → P → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) x) :
    delta v (fun y => ∑ i, f i y) x = ∑ i, delta v (f i) x :=
  D_sum3 _ f hf

def bracket (V W : P → Vect) (x : P) : Vect := fun k =>
  delta (V x) (fun y => W y k) x - delta (W x) (fun y => V y k) x

lemma delta_moving (v : Vect) {W : P → Vect} {f : P → ℝ} {x : P}
    (hW : DifferentiableAt ℝ W x) (hf : ContDiffAt ℝ 2 f x) :
    delta v (fun y => delta (W y) f y) x =
      ∑ i : A, (W x i * delta v (D (CKSRealizedRound.basis i) f) x +
        D (CKSRealizedRound.basis i) f x * delta v (fun y => W y i) x) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hfi (i : A) : DifferentiableAt ℝ (D (CKSRealizedRound.basis i) f) x :=
    (contDiffAt_D hf (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  simp only [delta_expansion (W _)]
  rw [delta_sum _ (fun i y => W y i * D (CKSRealizedRound.basis i) f y)
    (fun i => (hWi i).mul (hfi i))]
  apply Finset.sum_congr rfl
  intro i _
  exact delta_mul _ (hWi i) (hfi i)

lemma delta_commutator {V W : P → Vect} {f : P → ℝ} {x : P}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hf : ContDiffAt ℝ 2 f x) :
    delta (V x) (fun y => delta (W y) f y) x -
      delta (W x) (fun y => delta (V y) f y) x = delta (bracket V W x) f x := by
  rw [delta_moving _ hW hf, delta_moving _ hV hf]
  simp only [delta_expansion, bracket, Fin.sum_univ_three]
  rw [D_comm hf (CKSRealizedRound.basis 0) (CKSRealizedRound.basis 1),
    D_comm hf (CKSRealizedRound.basis 0) (CKSRealizedRound.basis 2),
    D_comm hf (CKSRealizedRound.basis 1) (CKSRealizedRound.basis 2)]
  ring

def nabla (Γ : P → Symbols) (v : Vect) (W : P → Vect) (x : P) : Vect := fun k =>
  delta v (fun y => W y k) x + ∑ i : A, ∑ j : A, v i * W x j * Γ x k i j

def curvature (Γ : P → Symbols) (V W Z : P → Vect) (x : P) : Vect :=
  nabla Γ (V x) (fun y => nabla Γ (W y) Z y) x -
    nabla Γ (W x) (fun y => nabla Γ (V y) Z y) x - nabla Γ (bracket V W x) Z x

def coordCurvature (Γ : P → Symbols) (x : P) (k l i j : A) : ℝ :=
  D (CKSRealizedRound.basis i) (fun y => Γ y k j l) x -
    D (CKSRealizedRound.basis j) (fun y => Γ y k i l) x +
    ∑ m : A, (Γ x m j l * Γ x k i m - Γ x m i l * Γ x k j m)

lemma delta_nabla (v : Vect) {Γ : P → Symbols} {W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hW : DifferentiableAt ℝ W x)
    (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    delta v (fun y => nabla Γ (W y) Z y k) x =
      delta v (fun y => delta (W y) (fun z => Z z k) y) x +
      ∑ i : A, ∑ j : A,
        (W x i * Z x j * delta v (fun y => Γ y k i j) x +
          Γ x k i j * (W x i * delta v (fun y => Z y j) x +
            Z x j * delta v (fun y => W y i) x)) := by
  have hWi (i : A) := differentiableAt_pi.mp hW i
  have hZi (i : A) := contDiffAt_pi.mp hZ i
  have hdZi (i j : A) : DifferentiableAt ℝ
      (D (CKSRealizedRound.basis i) (fun y => Z y j)) x :=
    (contDiffAt_D (hZi j) (m := 1) (by norm_num) _).differentiableAt (by norm_num)
  have hΓi (a i j : A) : DifferentiableAt ℝ (fun y => Γ y a i j) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp (differentiableAt_pi.mp hΓ a) i) j
  have hvZ : DifferentiableAt ℝ (fun y => delta (W y) (fun z => Z z k) y) x := by
    simp only [delta_expansion]
    exact DifferentiableAt.fun_sum fun i _ => (hWi i).mul (hdZi i k)
  have ht (i j : A) : DifferentiableAt ℝ
      (fun y => W y i * Z y j * Γ y k i j) x :=
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))).mul (hΓi k i j)
  have hs (i : A) : DifferentiableAt ℝ (fun y => ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun j _ => ht i j
  have hss : DifferentiableAt ℝ (fun y => ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x :=
    DifferentiableAt.fun_sum fun i _ => hs i
  change delta v (fun y => delta (W y) (fun z => Z z k) y +
    ∑ i : A, ∑ j : A, W y i * Z y j * Γ y k i j) x = _
  rw [delta_add _ hvZ hss, delta_sum _ _ hs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [delta_sum _ _ (ht i)]
  apply Finset.sum_congr rfl
  intro j _
  rw [delta_mul v (f := fun y => W y i * Z y j) (g := fun y => Γ y k i j)
    ((hWi i).mul ((hZi j).differentiableAt (by norm_num))) (hΓi k i j),
    delta_mul v (f := fun y => W y i) (g := fun y => Z y j)
      (hWi i) ((hZi j).differentiableAt (by norm_num))]

theorem curvature_coordinate {Γ : P → Symbols} {V W Z : P → Vect} {x : P}
    (hΓ : DifferentiableAt ℝ Γ x) (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) (hZ : ContDiffAt ℝ 2 Z x) (k : A) :
    curvature Γ V W Z x k = ∑ i : A, ∑ j : A, ∑ l : A,
      V x i * W x j * Z x l * coordCurvature Γ x k l i j := by
  change (delta (V x) (fun y => nabla Γ (W y) Z y k) x +
      ∑ i : A, ∑ j : A, V x i * nabla Γ (W x) Z x j * Γ x k i j) -
    (delta (W x) (fun y => nabla Γ (V y) Z y k) x +
      ∑ i : A, ∑ j : A, W x i * nabla Γ (V x) Z x j * Γ x k i j) -
    (delta (bracket V W x) (fun y => Z y k) x +
      ∑ i : A, ∑ j : A, bracket V W x i * Z x j * Γ x k i j) = _
  rw [delta_nabla _ hΓ hW hZ, delta_nabla _ hΓ hV hZ]
  have hc := delta_commutator hV hW (contDiffAt_pi.mp hZ k)
  rw [sub_eq_iff_eq_add.mp hc]
  simp only [nabla, coordCurvature, bracket, delta_expansion, Fin.sum_univ_three]
  ring

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAmbientCalculus
noncomputable section
open Matrix CKSAngularGeometry
open scoped BigOperators

def pair (γ : AmbientMat) (v w : Vect) : ℝ := ∑ i : A, ∑ j : A, γ i j * v i * w j

lemma inverse_metric_trace {γ : AmbientMat} (hp : γ.PosDef) (k i : A) :
    (∑ m : A, γ k m * γ⁻¹ i m) = if k = i then 1 else 0 := by
  have h : (γ * γ⁻¹) k i = (1 : AmbientMat) k i :=
    congrFun (congrFun (Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) k) i
  simpa only [Matrix.mul_apply, hermitian_real_symmetry hp.isHermitian.inv, Matrix.one_apply] using h

lemma sum_three_rotate (f : A → A → A → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem scalar_frame_contraction {γ : AmbientMat} (hp : γ.PosDef) (E : A → Vect)
    (hg : ∀ i j, (∑ a : A, E a i * E a j) = γ⁻¹ i j)
    (R : A → A → A → A → ℝ) :
    (∑ a : A, ∑ b : A, pair γ
      (fun k => ∑ i : A, ∑ j : A, ∑ l : A, E a i * E b j * E b l * R k l i j)
      (E a)) = ∑ j : A, ∑ l : A, γ⁻¹ j l * ∑ k : A, R k l k j := by
  calc
    _ = ∑ k : A, ∑ m : A, ∑ i : A, ∑ j : A, ∑ l : A,
        ∑ a : A, ∑ b : A,
          γ k m * E a i * E a m * E b j * E b l * R k l i j := by
      simp only [pair, Finset.mul_sum, Finset.sum_mul]
      conv_lhs =>
        rw [sum_three_rotate]
        arg 2; ext k
        rw [sum_three_rotate]
        arg 2; ext m
        rw [sum_three_rotate]
        arg 2; ext i
        rw [sum_three_rotate]
        arg 2; ext j
        rw [sum_three_rotate]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring
    _ = ∑ k : A, ∑ m : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (γ k m * γ⁻¹ i m) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro m _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      calc
        _ = (γ k m * (∑ a : A, E a i * E a m)) *
            (∑ b : A, E b j * E b l) * R k l i j := by
          simp only [Fin.sum_univ_three]
          ring
        _ = _ := by rw [hg, hg]
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A, ∑ m : A,
        (γ k m * γ⁻¹ i m) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2; ext i
        rw [Finset.sum_comm]
        arg 2; ext j
        rw [Finset.sum_comm]
    _ = ∑ k : A, ∑ i : A, ∑ j : A, ∑ l : A,
        (if k = i then 1 else 0) * γ⁻¹ j l * R k l i j := by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro l _
      rw [← Finset.sum_mul, ← Finset.sum_mul, inverse_metric_trace hp]
    _ = _ := by
      simp only [Fin.sum_univ_three]
      simp
      ring

end
end CKSAmbientCalculus

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def physicalSymbols (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) :
    CKSAmbientCalculus.Symbols := fun a i j => coordinateChristoffel G x i j a

lemma physicalSymbols_differentiableAt {G : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0) :
    DifferentiableAt ℝ (physicalSymbols G) x := by
  apply differentiableAt_pi.mpr; intro a
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  exact (coordinateChristoffel_contDiffAt hg h0 i j a).differentiableAt (by simp)

lemma curvatureVector_coordinate {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (a b c k : Fin 3) :
    curvatureVector G E x a b c k = ∑ i, ∑ j, ∑ l,
      E a x i * E b x j * E c x l *
        CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j := by
  have hz : ContDiffAt ℝ 2 (E c) x := (he c).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change CKSAmbientCalculus.curvature (physicalSymbols G) (E a) (E b) (E c) x k = _
  exact CKSAmbientCalculus.curvature_coordinate (physicalSymbols_differentiableAt hg h0)
    ((he a).differentiableAt (by simp)) ((he b).differentiableAt (by simp))
    hz k

lemma physical_scalar_coordinate_trace {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x = ∑ j, ∑ l, (G x)⁻¹ j l * ∑ k,
      CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l k j := by
  rw [actualScalar_curvature_trace hg he hp hs ho]
  have hc (a b) : curvatureVector G E x a b b = fun k => ∑ i, ∑ j, ∑ l,
      E a x i * E b x j * E b x l *
        CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j := by
    funext k
    exact curvatureVector_coordinate hg hp.det_pos.ne' he a b b k
  simp only [hc]
  change (∑ a, ∑ b, CKSAmbientCalculus.pair (G x)
    (fun k => ∑ i, ∑ j, ∑ l, E a x i * E b x j * E b x l *
      CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l i j) (E a x)) = _
  exact CKSAmbientCalculus.scalar_frame_contraction hp (fun a => E a x)
    (orthonormal_frame_completeness ho.self_of_nhds)
    (CKSAmbientCalculus.coordCurvature (physicalSymbols G) x)

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_gamma_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (a i j : Fin 3) :
    (physicalMetricJet G x).gamma a i j = (physicalMetricJet G x).gamma a j i := by
  rw [physicalMetricJet_gamma hs.self_of_nhds, physicalMetricJet_gamma hs.self_of_nhds]
  exact coordinateChristoffel_torsion hs i j a

lemma physicalMetricJet_dGamma_torsion {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (s a i j : Fin 3) :
    (physicalMetricJet G x).dGamma s a i j = (physicalMetricJet G x).dGamma s a j i := by
  rw [← physicalMetricJet_dGamma hg h0 hs, ← physicalMetricJet_dGamma hg h0 hs]
  apply D_congr
  filter_upwards [hs.eventually_nhds] with y hy
  exact coordinateChristoffel_torsion hy i j a

lemma physicalMetricJet_ricci {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (l j : Fin 3) :
    (∑ k, CKSAmbientCalculus.coordCurvature (physicalSymbols G) x k l k j) =
      (physicalMetricJet G x).ricci l j := by
  simp only [CKSAmbientCalculus.coordCurvature, physicalSymbols,
    physicalMetricJet_dGamma hg h0 hs, ← physicalMetricJet_gamma hs.self_of_nhds,
    Finset.sum_add_distrib, CKSRound.MetricJet.ricci]
  apply congrArg₂ (fun u v : ℝ => u + v)
  · apply Finset.sum_congr rfl; intro k _
    rw [physicalMetricJet_dGamma_torsion hg h0 hs k k j l,
      physicalMetricJet_dGamma_torsion hg h0 hs j k k l]
  · apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro m _
    rw [physicalMetricJet_gamma_torsion hs m j l,
      physicalMetricJet_gamma_torsion hs m k l]
    ring

theorem physicalMetricJet_scalar {G : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    actualFrameScalar G E x = (physicalMetricJet G x).scalar := by
  rw [physical_scalar_coordinate_trace hg he hp hs ho]
  simp only [physicalMetricJet_ricci hg hp.det_pos.ne' hs, CKSRound.MetricJet.scalar]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro j _
  change (G x)⁻¹ j l * _ = (G x)⁻¹ l j * _
  rw [hermitian_real_symmetry hp.isHermitian.inv j l]

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma matrix_inverse_trace_coordinates {g : AmbientMat} (hs : g.IsHermitian)
    (k : AmbientMat) : (g⁻¹*k).trace = ∑ a, ∑ b, g⁻¹ a b * k a b := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [hermitian_real_symmetry hs.inv b a]

lemma physicalMetricJet_trace {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) :
    ((G x)⁻¹*K x).trace = (physicalMetricJet G x).trace (physicalTensorJet K x) :=
  matrix_inverse_trace_coordinates hs (K x)

lemma matrix_tensor_norm_coordinates {g k : AmbientMat} (hs : g.IsHermitian)
    (hk : k.IsHermitian) :
    (g⁻¹*k*g⁻¹*k).trace = ∑ a, ∑ b, ∑ c, ∑ d,
      g⁻¹ a c * g⁻¹ b d * k a b * k c d := by
  simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext a
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  rw [hermitian_real_symmetry hs.inv c a, hermitian_real_symmetry hk d c]
  ring

lemma physicalMetricJet_normSq {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hs : (G x).IsHermitian) (hk : (K x).IsHermitian) :
    ((G x)⁻¹*K x*(G x)⁻¹*K x).trace =
      (physicalMetricJet G x).normSq (physicalTensorJet K x) :=
  matrix_tensor_norm_coordinates hs hk

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_dTrace {G K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x) (h0 : (G x).det ≠ 0)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i : Fin 3) :
    D (CKSRealizedRound.basis i) (fun y => ((G y)⁻¹*K y).trace) x =
      (physicalMetricJet G x).dTrace (physicalTensorJet K x) i := by
  have hki (a b) : DifferentiableAt ℝ (fun y => K y a b) x :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp hk a) b).differentiableAt (by simp)
  have hgi (a b) : DifferentiableAt ℝ (fun y => (G y)⁻¹ a b) x :=
    (matrix_inv_component_contDiffAt hg h0 a b).differentiableAt (by simp)
  have ht (a b) := (hgi a b).fun_mul (hki a b)
  calc
    _ = D (CKSRealizedRound.basis i) (fun y => ∑ a, ∑ b, (G y)⁻¹ a b*K y a b) x := by
      apply D_congr
      filter_upwards [hs] with y hy
      exact matrix_inverse_trace_coordinates hy (K y)
    _ = _ := by
      rw [D_sum3 _ _ (fun a => DifferentiableAt.fun_sum (fun b _ => ht a b))]
      unfold CKSRound.MetricJet.dTrace
      apply Finset.sum_congr rfl; intro a _
      rw [D_sum3 _ _ (ht a)]
      apply Finset.sum_congr rfl; intro b _
      rw [D_mul _ (hgi a b) (hki a b), physicalMetricJet_dInv hg h0]
      simp only [physicalTensorJet, physicalMetricJet]
      ring

lemma physicalMetricJet_tensorCovariant {G K : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hs : (G x).IsHermitian) (a b i : Fin 3) :
    coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (CKSRealizedRound.basis i) x =
        (physicalTensorJet K x).d a b i -
        (∑ c, (physicalMetricJet G x).gamma c a b * (physicalTensorJet K x).val c i) -
        (∑ c, (physicalMetricJet G x).gamma c a i * (physicalTensorJet K x).val b c) := by
  simp only [physicalMetricJet_gamma hs, physicalTensorJet]
  simp [coordinateTensorCovariant, coordinateConnectionVector, metricPair,
    CKSRealizedRound.basis, Pi.single_apply, mul_comm]

theorem physicalMetricJet_momentum {G K : PhysicalPoint → AmbientMat}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x) (hk : ContDiffAt ℝ ∞ K x)
    (h0 : (G x).det ≠ 0) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (i : Fin 3) :
    momentumCovector G K x i = (physicalMetricJet G x).momentum (physicalTensorJet K x) i := by
  simp only [momentumCovector, coordinateMomentum,
    matrix_inverse_trace_coordinates hs.self_of_nhds, Matrix.of_apply,
    physicalMetricJet_tensorCovariant hs.self_of_nhds, physicalMetricJet_dTrace hg hk h0 hs,
    CKSRound.MetricJet.momentum, CKSRound.MetricJet.tensorDivergence]
  rfl

end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

lemma physicalMetricJet_energy {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (he : ∀ i, ContDiffAt ℝ ∞ (E i) x) (hp : (G x).PosDef)
    (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian) (hks : (K x).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    physicalEnergy G K E x = (physicalMetricJet G x).energy (physicalTensorJet K x) := by
  unfold physicalEnergy CKSRound.MetricJet.energy
  rw [physicalMetricJet_scalar hg he hp hs ho, physicalMetricJet_trace hp.isHermitian,
    physicalMetricJet_normSq hp.isHermitian hks]

theorem physical_coordinate_DEC_iff {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (hg : ContDiffAt ℝ ∞ G x)
    (hk : ContDiffAt ℝ ∞ K x) (he : ∀ i, ContDiffAt ℝ ∞ (E i) x)
    (hp : (G x).PosDef) (hs : ∀ᶠ y in 𝓝 x, (G y).IsHermitian)
    (hks : (K x).IsHermitian)
    (ho : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (G y) (E i y) (E j y)=if i=j then 1 else 0) :
    physicalDEC G K E x ↔ CKSLocalBending.DEC (physicalMetricJet G x) (physicalTensorJet K x)
 := by
  have hn : metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) =
      CKSLocalBending.momentumSq (physicalMetricJet G x) (physicalTensorJet K x) := by
    simp only [metricPair, physicalMetricJet_momentum hg hk hp.det_pos.ne' hs]
    rfl
  unfold physicalDEC CKSLocalBending.DEC
  rw [hn, physicalMetricJet_energy hg he hp hs hks ho]

end
end CKSAngularGeometry

end






noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

structure SmoothOrthonormalAt (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (x : PhysicalPoint) : Prop where
  metric_smooth : ContDiffAt ℝ ∞ G x
  frame_smooth : ∀ i, ContDiffAt ℝ ∞ (E i) x
  positive : (G x).PosDef
  symmetric : ∀ᶠ y in 𝓝 x, (G y).IsHermitian
  orthonormal : ∀ᶠ y in 𝓝 x, ∀ i j, metricPair (G y) (E i y) (E j y) = if i=j then 1 else 0

structure FrameChartAt (φ : PhysicalPoint → PhysicalPoint)
    (G H : PhysicalPoint → AmbientMat) (E F : LocalFrame) (x : PhysicalPoint) : Prop where
  chart_smooth : ContDiffAt ℝ ∞ φ x
  source : SmoothOrthonormalAt G E (φ x)
  target : SmoothOrthonormalAt H F x
  frame_related : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ φ y (F i y) = E i (φ y)
  metric_related : ∀ v w, metricPair (H x) v w =
    metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma actualFrameBracket_eq_lieBracket {E : LocalFrame} {x : PhysicalPoint}
    (he : ∀ i, DifferentiableAt ℝ (E i) x) (i j : Fin 3) :
    actualFrameBracket E x i j = VectorField.lieBracket ℝ (E i) (E j) x := by
  ext k
  simp only [actualFrameBracket,D,VectorField.lieBracket,Pi.sub_apply,
    fderiv_apply (he j),fderiv_apply (he i),ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]
lemma FrameChartAt.bracket_related {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) (i j : Fin 3) :
    fderiv ℝ φ x (actualFrameBracket F x i j) = actualFrameBracket E (φ x) i j := by
  have hdφ := h.chart_smooth.differentiableAt (by simp)
  have hde k := (h.source.frame_smooth k).differentiableAt (by simp)
  have hdf k := (h.target.frame_smooth k).differentiableAt (by simp)
  have hr k : (fun y => fderiv ℝ φ y (F k y)) =ᶠ[𝓝 x] (fun y => E k (φ y)) :=
    h.frame_related.mono (fun y hy => hy k)
  rw [actualFrameBracket_eq_lieBracket hdf]
  rw [VectorField.fderiv_apply_lieBracket h.chart_smooth (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out) (hdf j) (hdf i)]
  rw [(hr j).fderiv_eq,(hr i).fderiv_eq,
    fderiv_fun_comp x (hde j) hdφ,fderiv_fun_comp x (hde i) hdφ]
  simp only [ContinuousLinearMap.comp_apply,h.frame_related.self_of_nhds]
  exact (actualFrameBracket_eq_lieBracket hde i j).symm
lemma FrameChartAt.bracket_coefficients {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) :
    frameBracketCoefficient H F x = frameBracketCoefficient G E (φ x) := by
  funext i j k
  unfold frameBracketCoefficient
  rw [h.metric_related,h.bracket_related,h.frame_related.self_of_nhds k]
lemma FrameChartAt.connection_coefficients {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x) :
    frameCoefficient H F x = frameCoefficient G E (φ x) := by
  have hs := h.source
  have ht := h.target
  rw [physical_frame_koszul (ht.metric_smooth.differentiableAt (by simp))
    (fun i => (ht.frame_smooth i).differentiableAt (by simp)) ht.positive ht.symmetric ht.orthonormal]
  rw [physical_frame_koszul (hs.metric_smooth.differentiableAt (by simp))
    (fun i => (hs.frame_smooth i).differentiableAt (by simp)) hs.positive hs.symmetric hs.orthonormal]
  rw [h.bracket_coefficients]

lemma D_chart_related {φ : PhysicalPoint → PhysicalPoint}
    {f g : PhysicalPoint → ℝ} {v w x : PhysicalPoint}
    (hφ : DifferentiableAt ℝ φ x) (hf : DifferentiableAt ℝ f (φ x))
    (hvw : fderiv ℝ φ x v = w) (hfg : g =ᶠ[𝓝 x] (fun y => f (φ y))) :
    D v g x = D w f (φ x) := by
  unfold D
  rw [hfg.fderiv_eq,fderiv_fun_comp x hf hφ,ContinuousLinearMap.comp_apply,hvw]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma frame_connection_direction_chart {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) (a i j k : Fin 3) :
    D (F a x) (fun y => frameCoefficient H F y i j k) x =
      D (E a (φ x)) (fun y => frameCoefficient G E y i j k) (φ x) := by
  have hx := h.self_of_nhds
  apply D_chart_related (hx.chart_smooth.differentiableAt (by simp))
    ((frameCoefficient_contDiffAt hx.source.metric_smooth hx.source.positive.det_pos.ne'
      hx.source.frame_smooth i j k).differentiableAt (by simp))
    (hx.frame_related.self_of_nhds a)
  filter_upwards [h] with y hy
  exact congrFun (congrFun (congrFun hy.connection_coefficients i) j) k
lemma actualFrameCurvature_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) (i j k l : Fin 3) :
    actualFrameCurvature H F x i j k l = actualFrameCurvature G E (φ x) i j k l := by
  unfold actualFrameCurvature
  rw [frame_connection_direction_chart h,frame_connection_direction_chart h,
    h.self_of_nhds.connection_coefficients,h.self_of_nhds.bracket_coefficients]
lemma actualFrameScalar_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y) :
    actualFrameScalar H F x = actualFrameScalar G E (φ x) := by
  unfold actualFrameScalar
  simp_rw [actualFrameCurvature_chart_covariance h]
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma frameTensor_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : FrameChartAt φ G H E F x)
    (hkl : ∀ v w, metricPair (L x) v w =
      metricPair (K (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w)) :
    frameTensor L F x = frameTensor K E (φ x) := by
  funext i j
  unfold frameTensor
  rw [hkl,h.frame_related.self_of_nhds i,h.frame_related.self_of_nhds j]
lemma frame_tensor_direction_chart {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) (a i j : Fin 3) :
    D (F a x) (fun y => frameTensor L F y i j) x =
      D (E a (φ x)) (fun y => frameTensor K E y i j) (φ x) := by
  have hx := h.self_of_nhds
  apply D_chart_related (hx.chart_smooth.differentiableAt (by simp))
    ((metricPair_contDiffAt hk (hx.source.frame_smooth i) (hx.source.frame_smooth j)).differentiableAt (by simp))
    (hx.frame_related.self_of_nhds a)
  filter_upwards [h,hkl] with y hy hky
  exact congrFun (congrFun (frameTensor_chart_covariance hy hky) i) j
lemma actualFrameTensorCovariant_chart_covariance {φ : PhysicalPoint → PhysicalPoint}
    {G H K L : PhysicalPoint → AmbientMat} {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) (i j k : Fin 3) :
    actualFrameTensorCovariant H L F x i j k = actualFrameTensorCovariant G K E (φ x) i j k := by
  unfold actualFrameTensorCovariant
  rw [frame_tensor_direction_chart h hk hkl,h.self_of_nhds.connection_coefficients,
    frameTensor_chart_covariance h.self_of_nhds hkl.self_of_nhds]

theorem actual_constraints_chart_covariance
    {φ : PhysicalPoint → PhysicalPoint} {G H K L : PhysicalPoint → AmbientMat}
    {E F : LocalFrame} {x : PhysicalPoint}
    (h : ∀ᶠ y in 𝓝 x, FrameChartAt φ G H E F y)
    (hk : ContDiffAt ℝ ∞ K (φ x))
    (hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (L y) v w =
      metricPair (K (φ y)) (fderiv ℝ φ y v) (fderiv ℝ φ y w)) :
    actualFrameScalar H F x = actualFrameScalar G E (φ x) ∧
    actualFrameEnergy H L F x = actualFrameEnergy G K E (φ x) ∧
    (∀ i, actualFrameMomentum H L F x i = actualFrameMomentum G K E (φ x) i)
 := by
  have hs := actualFrameScalar_chart_covariance h
  have ht := frameTensor_chart_covariance h.self_of_nhds hkl.self_of_nhds
  refine ⟨hs,?_,?_⟩
  · unfold actualFrameEnergy
    rw [hs,ht]
  · intro j
    unfold actualFrameMomentum
    simp_rw [actualFrameTensorCovariant_chart_covariance h hk hkl,
      frame_tensor_direction_chart h hk hkl]
end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def coordinatePullback (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x : PhysicalPoint) : AmbientMat := fun i j =>
  metricPair (G (φ x)) (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j))
def coordinatePullbackFrame (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (E : LocalFrame) : LocalFrame := fun i x => fderiv ℝ e.symm (e x) (E i (e x))
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma metricPair_sum_right (g : AmbientMat) (v : PhysicalPoint) (w : Fin 3 → PhysicalPoint) :
    metricPair g v (∑ i, w i) = ∑ i, metricPair g v (w i) := by
  simp only [metricPair,Fin.sum_univ_three,Pi.add_apply]
  ring
lemma coordinatePullback_pair (φ : PhysicalPoint → PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (x v w : PhysicalPoint) :
    metricPair (coordinatePullback φ G x) v w =
      metricPair (G (φ x)) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  conv_rhs => arg 2; rw [direction_expansion v]
  conv_rhs => arg 3; rw [direction_expansion w]
  simp only [map_sum,map_smul]
  simp only [metricPair_sum_left,metricPair_sum_right,metricPair_smul_left,
    metricPair_smul_right,Finset.mul_sum]
  change (∑ i, ∑ j, metricPair (G (φ x))
    (fderiv ℝ φ x (CKSRealizedRound.basis i))
    (fderiv ℝ φ x (CKSRealizedRound.basis j)) * v i * w j) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma metricPair_dotProduct (g : AmbientMat) (v : PhysicalPoint) :
    metricPair g v v = star v ⬝ᵥ (g *ᵥ v) := by
  simp only [metricPair,dotProduct,mulVec,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
lemma coordinatePullback_symmetric {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint} (hg : (G (φ x)).IsHermitian) :
    (coordinatePullback φ G x).IsHermitian := by
  ext i j
  simpa only [conjTranspose_apply,star_trivial,coordinatePullback] using
    metricPair_symm hg (fderiv ℝ φ x (CKSRealizedRound.basis j))
      (fderiv ℝ φ x (CKSRealizedRound.basis i))
lemma coordinatePullback_positive {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint} (hg : (G (φ x)).PosDef)
    (hφ : Function.Injective (fderiv ℝ φ x)) : (coordinatePullback φ G x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (coordinatePullback_symmetric hg.isHermitian)
  intro v hv
  rw [← metricPair_dotProduct,coordinatePullback_pair,metricPair_dotProduct]
  exact hg.dotProduct_mulVec_pos (fun h => hv (hφ (h.trans (map_zero _).symm)))
lemma coordinatePullback_smooth {φ : PhysicalPoint → PhysicalPoint}
    {G : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hφ : ContDiffAt ℝ ∞ φ x) (hg : ContDiffAt ℝ ∞ G (φ x)) :
    ContDiffAt ℝ ∞ (coordinatePullback φ G) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact metricPair_contDiffAt (hg.comp x hφ)
    ((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const)
    ((hφ.fderiv_right (by simp)).clm_apply contDiffAt_const)
lemma chart_fderiv_left_inverse
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x))
    (v : PhysicalPoint) : fderiv ℝ e.symm (e x) (fderiv ℝ e x v) = v := by
  have hEq : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id := e.eventually_left_inverse hx
  have hh := hEq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_fun_comp x hi he,fderiv_id] at hh
  exact congrArg (fun T : PhysicalPoint →L[ℝ] PhysicalPoint => T v) hh
lemma chart_fderiv_right_inverse
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x))
    (v : PhysicalPoint) : fderiv ℝ e x (fderiv ℝ e.symm (e x) v) = v := by
  have hh := chart_fderiv_left_inverse e.symm (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he) v
  simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using hh
lemma coordinatePullbackFrame_smooth
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint) (E : LocalFrame)
    {x : PhysicalPoint} (he : ContDiffAt ℝ ∞ e x) (hi : ContDiffAt ℝ ∞ e.symm (e x))
    (hE : ∀ i, ContDiffAt ℝ ∞ (E i) (e x)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (coordinatePullbackFrame e E i) x :=
  ((hi.fderiv_right (by simp)).comp x he).clm_apply ((hE i).comp x he)
end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
theorem actualFrameTensorCovariant_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) (i j k : Fin 3) :
    actualFrameTensorCovariant G K E x i j k =
      coordinateTensorCovariant G K (E i x) (E j x) (E k x) x := by
  have ho := h.orthonormal.self_of_nhds
  have hleft := metricPair_frame_left (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E j) x) (E k x)
  have hright := metricPair_frame_right (K x) (e := Matrix.of (fun a b => E a x b))
    ho (covariantVector G (E i x) (E k) x) (E j x)
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
    metricPair (K x) (E a x) (E k x)) = _ at hleft
  change (∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
    metricPair (K x) (E j x) (E a x)) = _ at hright
  rw [coordinateTensorCovariant_product_rule hk ((h.frame_smooth j).differentiableAt (by simp)) ((h.frame_smooth k).differentiableAt (by simp))]
  unfold actualFrameTensorCovariant
  rw [Finset.sum_add_distrib]
  change D (E i x) (fun y => metricPair (K y) (E j y) (E k y)) x -
    ((∑ a, metricPair (G x) (covariantVector G (E i x) (E j) x) (E a x)*
      metricPair (K x) (E a x) (E k x)) +
     ∑ a, metricPair (G x) (covariantVector G (E i x) (E k) x) (E a x)*
      metricPair (K x) (E j x) (E a x)) = _
  rw [hleft,hright]
  ring

lemma frame_trace_derivative_general {G K : PhysicalPoint → AmbientMat} {E : LocalFrame}
    {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x) (hk : DifferentiableAt ℝ K x)
    (e : PhysicalPoint) :
    (∑ i, D e (fun y => frameTensor K E y i i) x)=
      D e (fun y => ((G y)⁻¹*K y).trace) x := by
  change (∑ i, D e (fun y => metricPair (K y) (E i y) (E i y)) x) = _
  rw [← D_sum3 e _ (fun i => metricPair_differentiableAt hk ((h.frame_smooth i).differentiableAt (by simp)) ((h.frame_smooth i).differentiableAt (by simp)))]
  apply D_congr
  filter_upwards [h.orthonormal] with y hy
  exact frame_trace_exact (K y) (e := Matrix.of (fun i j => E i y j)) hy

theorem actualFrameEnergy_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : (K x).IsHermitian) :
    actualFrameEnergy G K E x =
      (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 := by
  have ho := h.orthonormal.self_of_nhds
  have ht := frame_trace_exact (K x) (e := Matrix.of (fun i j => E i x j)) ho
  have hn := frame_tensor_norm_exact hk (e := Matrix.of (fun i j => E i x j)) ho
  change (∑ i, metricPair (K x) (E i x) (E i x))=_ at ht
  change (∑ i, ∑ j, (metricPair (K x) (E i x) (E j x))^2)=_ at hn
  unfold actualFrameEnergy frameTensor
  rw [ht,hn]

theorem actualFrameMomentum_coordinate_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) (j : Fin 3) :
    actualFrameMomentum G K E x j=coordinateMomentum G K x (E j x) := by
  have ht := frame_trace_exact
    (Matrix.of (fun a b => coordinateTensorCovariant G K
      (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x))
    (e := Matrix.of (fun a b => E a x b)) h.orthonormal.self_of_nhds
  change (∑ i, metricPair
    (fun a b => coordinateTensorCovariant G K (CKSRealizedRound.basis a)
      (CKSRealizedRound.basis b) (E j x) x) (E i x) (E i x)) = _ at ht
  have hd : (∑ i, actualFrameTensorCovariant G K E x i i j) =
      ((G x)⁻¹ * Matrix.of (fun a b => coordinateTensorCovariant G K
        (CKSRealizedRound.basis a) (CKSRealizedRound.basis b) (E j x) x)).trace := by
    rw [← ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [actualFrameTensorCovariant_coordinate_general h hk]
    exact coordinateTensorCovariant_bilinear G K x (E i x) (E i x) (E j x)
  unfold actualFrameMomentum coordinateMomentum
  rw [hd,frame_trace_derivative_general h hk]

theorem physical_momentum_frame_norm_general {G K : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (h : SmoothOrthonormalAt G E x)
    (hk : DifferentiableAt ℝ K x) :
    (∑ a, (actualFrameMomentum G K E x a)^2)=
      metricPair (G x)⁻¹ (momentumCovector G K x) (momentumCovector G K x) := by
  conv_lhs => arg 2; ext a; rw [actualFrameMomentum_coordinate_general h hk,coordinateMomentum_expansion]
  exact covector_frame_square (momentumCovector G K x)
    (e := Matrix.of (fun i j => E i x j)) h.orthonormal.self_of_nhds

end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma smooth_coordinate_pullback_frame_at
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ContDiffAt ℝ ∞ e x) (hi : ContDiffAt ℝ ∞ e.symm (e x))
    (hSrc : SmoothOrthonormalAt G E (e x)) :
    FrameChartAt e G (coordinatePullback e G) E (coordinatePullbackFrame e E) x := by
  have hed := he.differentiableAt (by simp)
  have hid := hi.differentiableAt (by simp)
  have hEinj : Function.Injective (fderiv ℝ e x) := by
    intro v w h
    have hh := congrArg (fderiv ℝ e.symm (e x)) h
    simpa only [chart_fderiv_left_inverse e hx hed hid] using hh
  have hRel : ∀ᶠ y in 𝓝 x, ∀ i, fderiv ℝ e y (coordinatePullbackFrame e E i y) = E i (e y) := by
    filter_upwards [e.open_source.mem_nhds hx,(he.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      he.continuousAt.eventually ((hi.of_le (show 1 ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp))] with y hy hey hiy i
    exact chart_fderiv_right_inverse e hy (hey.differentiableAt (by simp))
      (hiy.differentiableAt (by simp)) _
  have hOrth : ∀ᶠ y in 𝓝 x, ∀ i j,
      metricPair (coordinatePullback e G y) (coordinatePullbackFrame e E i y)
        (coordinatePullbackFrame e E j y) = if i=j then 1 else 0 := by
    filter_upwards [hRel,he.continuousAt.eventually hSrc.orthonormal] with y hyr hyo i j
    rw [coordinatePullback_pair,hyr i,hyr j,hyo]
  refine ⟨he,hSrc,?_,hRel,coordinatePullback_pair e G x⟩
  refine ⟨coordinatePullback_smooth he hSrc.metric_smooth,
    coordinatePullbackFrame_smooth e E he hi hSrc.frame_smooth,
    coordinatePullback_positive hSrc.positive hEinj,?_,hOrth⟩
  exact (he.continuousAt.eventually hSrc.symmetric).mono fun _ h => coordinatePullback_symmetric h

theorem local_coordinate_DEC_pullback
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 (e x), SmoothOrthonormalAt G E y)
    (hK : ContDiffAt ℝ ∞ K (e x)) (hs : (K (e x)).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) ↔
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) := by
  have h : ∀ᶠ y in 𝓝 x, FrameChartAt e G (coordinatePullback e G) E
      (coordinatePullbackFrame e E) y := by
    filter_upwards [e.open_source.mem_nhds hx,he,
      he.self_of_nhds.continuousAt.eventually hi,he.self_of_nhds.continuousAt.eventually hE]
      with y hy hey hiy hEy
    exact smooth_coordinate_pullback_frame_at e G E hy hey hiy hEy
  have hc := h.self_of_nhds
  have hk' := coordinatePullback_smooth hc.chart_smooth hK
  have hkSymm := coordinatePullback_symmetric hs
  have hkl : ∀ᶠ y in 𝓝 x, ∀ v w, metricPair (coordinatePullback e K y) v w =
      metricPair (K (e y)) (fderiv ℝ e y v) (fderiv ℝ e y w) :=
    Eventually.of_forall fun y => coordinatePullback_pair e K y
  obtain ⟨_,hC,hJ⟩ := actual_constraints_chart_covariance h hK hkl
  have hδ : physicalEnergy (coordinatePullback e G) (coordinatePullback e K)
      (coordinatePullbackFrame e E) x = physicalEnergy G K E (e x) := by
    rw [actualFrameEnergy_coordinate_general hc.target hkSymm,
      actualFrameEnergy_coordinate_general hc.source hs] at hC
    exact hC
  rw [← physical_coordinate_DEC_iff hc.target.metric_smooth hk' hc.target.frame_smooth
    hc.target.positive hc.target.symmetric hkSymm hc.target.orthonormal,
    ← physical_coordinate_DEC_iff hc.source.metric_smooth hK hc.source.frame_smooth
      hc.source.positive hc.source.symmetric hs hc.source.orthonormal]
  unfold physicalDEC
  rw [← physical_momentum_frame_norm_general hc.target (hk'.differentiableAt (by simp)),
    ← physical_momentum_frame_norm_general hc.source (hK.differentiableAt (by simp)), hδ]
  simp_rw [hJ]
end
end CKSAngularGeometry

end








noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma coordinatePullback_symm
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint) (G : PhysicalPoint → AmbientMat)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : DifferentiableAt ℝ e x) (hi : DifferentiableAt ℝ e.symm (e x)) :
    coordinatePullback e.symm (coordinatePullback e G) (e x) = G (e x) := by
  ext i j
  change metricPair (coordinatePullback e G (e.symm (e x)))
    (fderiv ℝ e.symm (e x) (CKSRealizedRound.basis i))
    (fderiv ℝ e.symm (e x) (CKSRealizedRound.basis j)) = _
  rw [e.left_inv hx,coordinatePullback_pair,
    chart_fderiv_right_inverse e hx he hi,chart_fderiv_right_inverse e hx he hi]
  simp [metricPair,CKSRealizedRound.basis,Pi.single_apply,mul_ite]
lemma physicalMetricJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalMetricJet G x = physicalMetricJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  have hd (a i j) : D (CKSRealizedRound.basis a) (fun y => G y i j) =ᶠ[𝓝 x]
      D (CKSRealizedRound.basis a) (fun y => H y i j) :=
    (hc i j).eventually_nhds.mono fun _ hh => D_congr hh _
  unfold physicalMetricJet
  congr 1
  · exact congrArg Inv.inv h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
  · funext a b i j
    exact D_congr (hd b i j) _
lemma physicalTensorJet_congr {G H : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (h : G =ᶠ[𝓝 x] H) : physicalTensorJet G x = physicalTensorJet H x := by
  have hc (i j) : (fun y => G y i j) =ᶠ[𝓝 x] (fun y => H y i j) :=
    h.mono fun _ hh => congrFun (congrFun hh i) j
  unfold physicalTensorJet
  congr 1
  · exact h.self_of_nhds
  · funext a i j
    exact D_congr (hc i j) _
theorem local_coordinate_DEC_pushforward
    (e : OpenPartialHomeomorph PhysicalPoint PhysicalPoint)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    {x : PhysicalPoint} (hx : x ∈ e.source)
    (he : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y)
    (hi : ∀ᶠ y in 𝓝 (e x), ContDiffAt ℝ ∞ e.symm y)
    (hE : ∀ᶠ y in 𝓝 x, SmoothOrthonormalAt (coordinatePullback e G) E y)
    (hK : ContDiffAt ℝ ∞ (coordinatePullback e K) x)
    (hs : (coordinatePullback e K x).IsHermitian) :
    CKSLocalBending.DEC (physicalMetricJet G (e x)) (physicalTensorJet K (e x)) ↔
    CKSLocalBending.DEC (physicalMetricJet (coordinatePullback e G) x)
      (physicalTensorJet (coordinatePullback e K) x) := by
  have hEq (A : PhysicalPoint → AmbientMat) :
      coordinatePullback e.symm (coordinatePullback e A) =ᶠ[𝓝 (e x)] A := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx),hi,
      (e.symm.continuousAt (e.map_source hx)).eventually (e.left_inv hx ▸ he)] with y hy hiy hey
    have hh := coordinatePullback_symm e A (e.map_target hy)
      (hey.differentiableAt (by simp)) (by simpa only [e.right_inv hy] using hiy.differentiableAt (by simp))
    simpa only [e.right_inv hy] using hh
  have h := local_coordinate_DEC_pullback e.symm (coordinatePullback e G)
    (coordinatePullback e K) E (e.map_source hx) hi
    (by simpa only [e.left_inv hx,OpenPartialHomeomorph.symm_symm] using he)
    (by simpa only [e.left_inv hx] using hE)
    (by simpa only [e.left_inv hx] using hK)
    (by simpa only [e.left_inv hx] using hs)
  rw [physicalMetricJet_congr (hEq G),physicalTensorJet_congr (hEq K),e.left_inv hx] at h
  exact h
end
end CKSAngularGeometry

end


noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter Set CKSSphericalChart CKSRealizedRound
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma SmoothOrthonormalAt.congr_metric {G H : PhysicalPoint → AmbientMat}
    {E : LocalFrame} {x : PhysicalPoint} (hg : SmoothOrthonormalAt G E x)
    (h : H =ᶠ[𝓝 x] G) : SmoothOrthonormalAt H E x := by
  refine ⟨hg.metric_smooth.congr_of_eventuallyEq h, hg.frame_smooth, ?_, ?_, ?_⟩
  · rw [h.self_of_nhds]
    exact hg.positive
  · filter_upwards [h,hg.symmetric] with y hy hs
    rwa [hy]
  · filter_upwards [h,hg.orthonormal] with y hy ho
    rwa [hy]

end
end CKSAngularGeometry

end












noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry CKSTangentCoefficients CKSCartesianOuter CKSInducedSphere CKSSphericalChart
open scoped BigOperators
lemma spatialMatrix_apply (F : E → AmbientMat) (x v w : E) :
    spatialMatrix F x v w = pair (F x) v w := by
  have hh := matrixBilinear_apply (fun i j => F x i j) (fun i => v i) (fun i => w i)
  change spatialMatrix F x v w = _ at hh
  rw [hh]
  simp only [pair,Fin.sum_univ_three]
  ring

end
end CKSLorentz

end










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

lemma sourceTensor_smoothAt {f : SourceTensorFields} {y : Point}
    (hf : f.SmoothAt y) (hy : y 0 ≠ 0) : ContDiffAt ℝ ∞ (sourceTensor f) y :=
  metricBlock_smoothAt (sourceRadialK_smoothAt hf) hf.kb (sourceTangentialK_smoothAt hf.base hy)
end
end CKSMixedGeometry

end




noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Filter CKSAngularSlice
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
lemma foliationMetric_lapse_ne_zero {U : ℝ} {γ : Mat} {s : Point}
    (hp : (foliationMetric U γ s).PosDef) : U ≠ 0 := by
  intro h0
  let v : PhysicalPoint := ![1,-s 0,-s 1]
  have hv : v ≠ 0 := by intro h; have hh := congrFun h 0; norm_num [v] at hh
  have h := hp.dotProduct_mulVec_pos hv
  rw [foliationMetric_quadratic U (metricBlock_leaf_posDef hp).isHermitian s v,h0] at h
  have hz : (fun a : Fin 2 => v a.succ+s a*v 0) = 0 := by
    ext a; fin_cases a <;> simp [v]
  rw [hz] at h
  simp at h
lemma foliation_smoothOrthonormalAt {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : U x ≠ 0)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    SmoothOrthonormalAt (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x := by
  have ha := (foliation_actualAdaptedAt hU hγ hs h0 hp).self_of_nhds
  exact ⟨foliationMetric_contDiffAt hU hγ hs h0,
    adaptedFrame_contDiffAt hU hγ hs hp.self_of_nhds,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1⟩
lemma radialMassLapse_denominators {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {t F : PhysicalPoint → ℝ} {x : PhysicalPoint} (hu : radialMassLapse γ s t F x ≠ 0) :
    radialExpansion γ s x ≠ 0 ∧ radialMassRadical t F x ≠ 0 := by
  change Real.sqrt (radialMassRadical t F x) / radialExpansion γ s x ≠ 0 at hu
  constructor
  · exact (div_ne_zero_iff.mp hu).2
  · intro h
    apply (div_ne_zero_iff.mp hu).1
    rw [h,Real.sqrt_zero]
lemma physical_collar_frame_lapse {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hp : (physicalCollarMetric R f x).PosDef) : physicalCollarU R f x ≠ 0 := by
  exact foliationMetric_lapse_ne_zero (U := physicalCollarU R f x)
    (γ := physicalCollarGamma R f x) (s := physicalCollarShift R f x) hp
lemma physical_collar_frame_leaf {R : ℝ} {f : LogCollarData} {x : PhysicalPoint}
    (hp : (physicalCollarMetric R f x).PosDef) : (physicalCollarGamma R f x).PosDef := by
  have h := hp.submatrix (Fin.succ_injective 2)
  simpa only [physicalCollarMetric,foliationMetric,metricBlock_submatrix] using h
lemma physical_collar_smoothOrthonormalAt {R : ℝ} (hR : 0 < R) {f : LogCollarData}
    {x : PhysicalPoint} (hr : x 0 ≠ 0) (hf : f.SmoothAt (radiusLogPoint x))
    (hσ : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.sigma z).IsHermitian)
    (he : ∀ᶠ z in 𝓝 (radiusLogPoint x), (f.metricError z).IsHermitian)
    (hp : (physicalCollarMetric R f x).PosDef) :
    SmoothOrthonormalAt (physicalCollarMetric R f) (physicalCollarFrame R f) x := by
  have hU0 := physical_collar_frame_lapse hp
  have hγ := physical_collar_frame_leaf hp
  obtain ⟨hd,hu⟩ := radialMassLapse_denominators hU0
  have hUs := physicalCollarU_smoothAt hR hr hf hγ hd hu
  have hγs := physicalCollarGamma_smoothAt R hr hf
  have hss := physicalCollarShift_smoothAt R hr hf
  have hge := physicalCollarGamma_eventually_posDef hr hf hσ he hγ
  exact foliation_smoothOrthonormalAt (U := physicalCollarU R f)
    (γ := physicalCollarGamma R f) (s := physicalCollarShift R f) hUs hγs hss hU0 hge
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_orthonormal {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    SmoothOrthonormalAt (sourceMetric (q.patch i).fields.base)
      (sourceFrame (q.patch i).fields.base) y := by
  have hr : y 0 ≠ 0 := (q.radius_pos.trans hy.1).ne'
  have hf := q.source_smooth i y hy
  have hp := q.positive_eventually i hy
  have hγ : ∀ᶠ z in 𝓝 y, (sourceGamma (q.patch i).fields.base z).PosDef :=
    hp.mono fun _ h => metricBlock_leaf_posDef h
  have h := foliation_smoothOrthonormalAt
    (sourceLapse_smoothAt hf.base hr hp.self_of_nhds) (sourceGamma_smoothAt hf.base hr)
    (sourceShift_smoothAt hf.base hr hp.self_of_nhds) (sourceLapse_pos hp.self_of_nhds).ne' hγ
  exact h.congr_metric (hp.mono (fun z hz => (source_metric_foliation hz).symm))
lemma SourceCollarAtlas.collar_data_smooth {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    (sourceCollarData (q.patch i).fields.logFields).SmoothAt (radiusLogPoint y) := by
  have hr : 0 < y 0 := q.radius_pos.trans hy.1
  have hf := q.source_smooth i y hy
  have hp := q.positive_eventually i hy
  have hs : determinant ((q.patch i).fields.base.logFields.sigma (radiusLogPoint y)) ≠ 0 := by
    change determinant (angularRoundMetric (q.patch i).patch.param (angularProjection (radiusLogPoint y))) ≠ 0
    rw [angularProjection_radiusLogPoint,determinant_eq]
    exact ((q.patch i).patch.roundMetric_posDef ((q.patch i).region_target hy.2)).det_pos.ne'
  apply sourceCollarData_smoothAt _ _ hs
  · rwa [logRadiusChart_radiusLogPoint hr]
  · rwa [logRadiusChart_radiusLogPoint hr]
lemma SourceCollarAtlas.collar_symmetries {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region) :
    (∀ᶠ z in 𝓝 (radiusLogPoint y), ((sourceCollarData (q.patch i).fields.logFields).sigma z).IsHermitian) ∧
    (∀ᶠ z in 𝓝 (radiusLogPoint y), ((sourceCollarData (q.patch i).fields.logFields).metricError z).IsHermitian) ∧
    (∀ᶠ z in 𝓝 (radiusLogPoint y), ((sourceCollarData (q.patch i).fields.logFields).tauDivR2 z).IsHermitian) := by
  have hr : 0 < y 0 := q.radius_pos.trans hy.1
  apply sourceCollar_symmetries
  · rw [logRadiusChart_radiusLogPoint hr]; exact q.positive_eventually i hy
  · apply (q.patch i).sigma_eventually
    simpa only [angularProjection_radiusLogPoint] using hy.2
  · rw [logRadiusChart_radiusLogPoint hr]; exact q.symmetric_eventually i hy
lemma SourceCollarAtlas.collar_orthonormal_eventually {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) (i : ι) {R : ℝ} (hR : 0 < R) {y : CKSMixedGeometry.Point}
    (hy : y ∈ angularRadialTail q.radius (q.patch i).region)
    (hp : (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields) y).PosDef) :
    ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt
      (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
      (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) z := by
  have hr : y 0 ≠ 0 := (q.radius_pos.trans hy.1).ne'
  have hf := q.collar_data_smooth i hy
  obtain ⟨hσ,he,_⟩ := q.collar_symmetries i hy
  have hU0 : physicalCollarU R (sourceCollarData (q.patch i).fields.logFields) y ≠ 0 :=
    physical_collar_frame_lapse hp
  have hγ := physicalCollarGamma_eventually_posDef hr hf hσ he (physical_collar_frame_leaf hp)
  obtain ⟨hd,hu⟩ := radialMassLapse_denominators hU0
  have hUs := physicalCollarU_smoothAt hR hr hf (physical_collar_frame_leaf hp) hd hu
  filter_upwards [(angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy,
    hγ,hUs.continuousAt.eventually_ne hU0] with z hz hgz huz
  obtain ⟨hσz,hez,_⟩ := q.collar_symmetries i hz
  exact physical_collar_smoothOrthonormalAt hR (q.radius_pos.trans hz.1).ne'
    (q.collar_data_smooth i hz) hσz hez (foliationMetric_posDef huz hgz _)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice Set Filter
open scoped ContDiff Topology

lemma polarCartesianChart_mem (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    y ∈ (polarCartesianChart P hr hy).source :=
  (cartesianPolar_smoothAt P hy).mem_toOpenPartialHomeomorph_source
    (polarDerivative_hasFDerivAt P hr hy) (by simp)
lemma polarCartesianChart_smooth (P : SmoothAngularPatch) {y : Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target) :
    (∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ (polarCartesianChart P hr hy) z) ∧
    ∀ᶠ z in 𝓝 (cartesianPolar P y), ContDiffAt ℝ ∞ (polarCartesianChart P hr hy).symm z := by
  let e := polarCartesianChart P hr hy
  have hex : y ∈ e.source := polarCartesianChart_mem P hr hy
  have hnear : ∀ᶠ z in 𝓝 y, 0 < z 0 ∧ angularProjection z ∈ P.chart.target :=
    Filter.inter_mem ((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr)
      (angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy))
  refine ⟨hnear.mono (fun z hz => cartesianPolar_smoothAt P hz.2),?_⟩
  have hn : ∀ᶠ z in 𝓝 (e y), 0 < (e.symm z) 0 ∧ angularProjection (e.symm z) ∈ P.chart.target :=
    (e.symm.continuousAt (e.map_source hex)).eventually (e.left_inv hex ▸ hnear)
  filter_upwards [e.open_target.mem_nhds (e.map_source hex),hn] with z hz hreg
  exact e.contDiffAt_symm hz (polarDerivative_hasFDerivAt P hreg.1 hreg.2)
    (cartesianPolar_smoothAt P hreg.2)
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularGeometry
open scoped BigOperators
lemma spatialCoefficients_pair (A : SpatialTensor) (y v w : PhysicalPoint) :
    metricPair (spatialCoefficients A y) v w =
      A (CKSCartesianOuter.toPoint.symm y) (CKSCartesianOuter.toPoint.symm v)
        (CKSCartesianOuter.toPoint.symm w) := by
  conv_rhs => rw [← CKSMixedGeometry.sum_coordinate_basis v,
    ← CKSMixedGeometry.sum_coordinate_basis w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,spatialCoefficients,metricPair]
  simp only [Fin.sum_univ_three]
  ring
lemma spatialCoefficients_pullback (P : SmoothAngularPatch) (A : SpatialTensor)
    {y : CKSMixedGeometry.Point} (hy : angularProjection y ∈ P.chart.target) :
    coordinatePullback (cartesianPolar P) (spatialCoefficients A) y =
      fun i j => polarTensorComponents P A i j y := by
  ext i j
  unfold coordinatePullback
  rw [spatialCoefficients_pair,cartesianPolar_fderiv P hy]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply,cartesianPolar,polarTensorComponents]
  rfl
lemma spatialCoefficients_spatialMatrix (F : E → AmbientMat) :
    spatialCoefficients (spatialMatrix F) = fun y => F (CKSCartesianOuter.toPoint.symm y) := by
  funext y i j
  unfold spatialCoefficients
  rw [spatialMatrix_apply]
  simp [CKSSphericalChart.pair,CKSMixedGeometry.basis,ite_mul,mul_ite]
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma spatialDEC_congr {A B C D : SpatialTensor} {x : E}
    (hA : A =ᶠ[𝓝 x] C) (hB : B =ᶠ[𝓝 x] D) : spatialDEC A B x ↔ spatialDEC C D x := by
  have he (P Q : SpatialTensor) (h : P =ᶠ[𝓝 x] Q) :
      spatialCoefficients P =ᶠ[𝓝 (CKSCartesianOuter.toPoint x)] spatialCoefficients Q := by
    have hh := CKSCartesianOuter.toPoint.symm.continuous.continuousAt.eventually
      (CKSCartesianOuter.toPoint.symm_apply_apply x ▸ h)
    filter_upwards [hh] with y hy
    ext i j
    change P (CKSCartesianOuter.toPoint.symm y) _ _ = Q (CKSCartesianOuter.toPoint.symm y) _ _
    rw [hy]
  unfold spatialDEC
  rw [physicalMetricJet_congr (he A C hA),physicalTensorJet_congr (he B D hB)]
lemma spatialDEC_of_polar {A B : SpatialTensor} (P : SmoothAngularPatch)
    {y : CKSMixedGeometry.Point} (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (G K : PhysicalPoint → AmbientMat) (E : LocalFrame)
    (hg : (fun z => fun i j => polarTensorComponents P A i j z) =ᶠ[𝓝 y] G)
    (hk : (fun z => fun i j => polarTensorComponents P B i j z) =ᶠ[𝓝 y] K)
    (hE : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt G E z)
    (hK : ContDiffAt ℝ ∞ K y) (hs : (K y).IsHermitian)
    (hDEC : physicalDEC G K E y) : spatialDEC A B (polarParam P y) := by
  let e := polarCartesianChart P hr hy
  have hsrc : y ∈ e.source := polarCartesianChart_mem P hr hy
  obtain ⟨he,hi⟩ := polarCartesianChart_smooth P hr hy
  have hEq (F : SpatialTensor) : coordinatePullback e (spatialCoefficients F) =ᶠ[𝓝 y]
      (fun z => fun i j => polarTensorComponents P F i j z) := by
    filter_upwards [angularProjection.continuous.continuousAt.preimage_mem_nhds
      (P.chart.open_target.mem_nhds hy)] with z hz
    exact spatialCoefficients_pullback P F hz
  have hG := (hEq A).trans hg
  have hT := (hEq B).trans hk
  have hframe : ∀ᶠ z in 𝓝 y, SmoothOrthonormalAt (coordinatePullback e (spatialCoefficients A)) E z := by
    filter_upwards [hE,hG.eventually_nhds] with z hz heq
    exact hz.congr_metric heq
  have hTsm := hK.congr_of_eventuallyEq hT
  have hTs : (coordinatePullback e (spatialCoefficients B) y).IsHermitian := by
    rwa [hT.self_of_nhds]
  have ht := local_coordinate_DEC_pushforward e (spatialCoefficients A) (spatialCoefficients B) E
    hsrc he hi hframe hTsm hTs
  apply ht.mpr
  rw [physicalMetricJet_congr hG,physicalTensorJet_congr hT]
  have h := hE.self_of_nhds
  exact (physical_coordinate_DEC_iff h.metric_smooth hK h.frame_smooth h.positive h.symmetric hs
    h.orthonormal).mp hDEC
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
lemma SourceCollarAtlas.source_spatial_DEC {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι)
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v)
    {x : E} (hx : q.radius < ‖x‖) : spatialDEC (sourceSpatial A) (sourceSpatial B) x := by
  let i := q.localIndex x
  have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
    ⟨norm_pos_iff.mp (q.radius_pos.trans hx),Classical.choose_spec (q.covers (spatialDirection x))⟩
  obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
  let y := polarInverse (q.patch i).patch x
  have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
  have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rwa [hyr],hyw⟩
  have hn : ∀ᶠ z in 𝓝 y, z ∈ angularRadialTail q.radius (q.patch i).region :=
    (angularRadialTail_open q.radius (q.patch i).region_open).mem_nhds hy
  have he : ∀ᶠ z in 𝓝 y,
      (fun a b => polarTensorComponents (q.patch i).patch (sourceSpatial A) a b z) =
        sourceMetric (q.patch i).fields.base z ∧
      (fun a b => polarTensorComponents (q.patch i).patch (sourceSpatial B) a b z) =
        sourceTensor (q.patch i).fields z := by
    filter_upwards [hn] with z hz
    have hz0 := q.radius_pos.trans hz.1
    have hzr : q.radius < ‖polarParam (q.patch i).patch z‖ := by
      rw [polarParam_norm _ hz0.le]; exact hz.1
    have h := spatial_source_reconstruction (q.patch i) hz0 ((q.patch i).region_target hz.2)
      (hA _ hzr) (hB _ hzr)
    exact ⟨h.1.symm,h.2.1.symm⟩
  have h := spatialDEC_of_polar (q.patch i).patch hy0 hyt
    (sourceMetric (q.patch i).fields.base) (sourceTensor (q.patch i).fields)
    (sourceFrame (q.patch i).fields.base) (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)
    (hn.mono fun z hz => q.source_orthonormal i hz)
    (sourceTensor_smoothAt (q.source_smooth i y hy) hy0.ne')
    (metricBlock_hermitian _ _ (q.source_symmetric i y hy)) (q.source_DEC i y hy)
  rwa [hyx] at h
end
end CKSLorentz

end

















noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter
open scoped ContDiff Topology
lemma polar_components_of_lift_eq (P : SmoothAngularPatch) (A : SpatialTensor)
    (F : CKSMixedGeometry.Point → AmbientMat) {y : CKSMixedGeometry.Point}
    (hr : 0 < y 0) (hy : angularProjection y ∈ P.chart.target)
    (he : A =ᶠ[𝓝 (polarParam P y)] polarLift P F) :
    (fun z => fun i j => polarTensorComponents P A i j z) =ᶠ[𝓝 y] F := by
  filter_upwards [(polarParam_contDiffAt P hy).continuousAt.eventually he,
    (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hr,
    angularProjection.continuous.continuousAt.preimage_mem_nhds (P.chart.open_target.mem_nhds hy)]
    with z hz hz0 hzt
  ext i j
  change A (polarParam P z) _ _ = _
  rw [hz]
  exact polarLift_components P F hz0 hzt i j
end
end CKSLorentz

end

noncomputable section
namespace CKSLorentz
noncomputable section
open CKSMixedGeometry CKSAngularSlice CKSAngularGeometry Set Filter CKSSphericalHarmonics
open scoped ContDiff Topology

theorem actual_same_end_DEC {A B : SpatialTensor} {ι : Type*}
    (q : SourceCollarAtlas A B ι) {M : Sphere → ℝ} (hM : SmoothSphere M)
    (hmass : q.HasMassAspect M) (m : ℝ) (hcharge : bondiCharge M = (m,0))
    (hA : ∀ x, q.radius < ‖x‖ → ∀ v w, A x v w = A x w v)
    (hB : ∀ x, q.radius < ‖x‖ → ∀ v w, B x v w = B x w v) :
    ∃ S R₀ : ℝ, 1 ≤ S ∧ q.radius < S ∧ S < R₀ ∧
      ∀ R ≥ R₀, ∀ x : E, S < ‖x‖ →
        spatialDEC (q.replacementMetric (heatDatum M hM) m R)
          (q.replacementTensor (heatDatum M hM) m R) x := by
  obtain ⟨S,R₁,hS,hqS,hS₁,hprep⟩ := q.replacement_localization hM hmass m hcharge hA hB
  obtain ⟨R₂,hR₂,houter⟩ := CKSCartesianOuter.constructed_cartesian_outer_DEC
    (heatDatum M hM) (heatDatum_smooth hM) m
  refine ⟨S,max R₁ R₂,hS,hqS,hS₁.trans_le (le_max_left _ _),?_⟩
  intro R hR x hx
  have h1 := (le_max_left R₁ R₂).trans hR
  have h2 := (le_max_right R₁ R₂).trans hR
  have hRp : 0 < R := by linarith
  obtain ⟨hpoint,hlocal⟩ := hprep R h1
  by_cases hi : ‖x‖ < R
  · have he : ∀ᶠ z in 𝓝 x,
        q.replacementMetric (heatDatum M hM) m R z = sourceSpatial A z ∧
        q.replacementTensor (heatDatum M hM) m R z = sourceSpatial B z := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hi] with z hz
      simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,ite_eq_left hz.le]
      exact ⟨trivial,trivial⟩
    exact (spatialDEC_congr (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)).mpr
      (q.source_spatial_DEC hA hB (hqS.trans hx))
  · by_cases ho : 3*R < ‖x‖
    · have he : ∀ᶠ z in 𝓝 x,
          q.replacementMetric (heatDatum M hM) m R z =
            spatialMatrix (CKSCartesianOuter.metric (heatDatum M hM) m R) z ∧
          q.replacementTensor (heatDatum M hM) m R z =
            spatialMatrix (CKSCartesianOuter.tensor (heatDatum M hM) m R) z := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds ho] with z hz
        simp only [SourceCollarAtlas.replacementMetric,SourceCollarAtlas.replacementTensor,
          ite_eq_right (by linarith : ¬ ‖z‖ ≤ R),ite_eq_right (not_le.mpr hz)]
        exact ⟨trivial,trivial⟩
      apply (spatialDEC_congr (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)).mpr
      unfold spatialDEC
      rw [spatialCoefficients_spatialMatrix,spatialCoefficients_spatialMatrix]
      exact houter R h2 x ho.le
    · have hr : R ≤ ‖x‖ := le_of_not_gt hi
      have ht : ‖x‖ ≤ 3*R := le_of_not_gt ho
      let i := q.localIndex x
      have hc : x ∈ polarCone (q.patch i).patch (q.patch i).region :=
        ⟨norm_pos_iff.mp (hRp.trans_le hr),Classical.choose_spec (q.covers (spatialDirection x))⟩
      obtain ⟨hy0,hyw,hyt,hyx⟩ := polarCone_inverse (q.patch i).patch hc
      let y := polarInverse (q.patch i).patch x
      have hyr : y 0 = ‖x‖ := by simp [y,polarInverse]
      have hy : y ∈ angularRadialTail q.radius (q.patch i).region := ⟨by rw [hyr]; exact hqS.trans hx,hyw⟩
      have hpr := hpoint i y (by rwa [hyr]) (by rwa [hyr]) hyw
      have hel := hlocal i x hr ht hc
      have hg := polar_components_of_lift_eq (q.patch i).patch
        (q.replacementMetric (heatDatum M hM) m R)
        (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields)) hy0 hyt
        (by rw [hyx]; exact hel.mono (fun _ h => h.1))
      have hk := polar_components_of_lift_eq (q.patch i).patch
        (q.replacementTensor (heatDatum M hM) m R)
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields)) hy0 hyt
        (by rw [hyx]; exact hel.mono (fun _ h => h.2))
      have h := spatialDEC_of_polar (q.patch i).patch hy0 hyt
        (physicalCollarMetric R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarTensor R (sourceCollarData (q.patch i).fields.logFields))
        (physicalCollarFrame R (sourceCollarData (q.patch i).fields.logFields)) hg hk
        (q.collar_orthonormal_eventually i hRp hy hpr.1.metric_positive)
        hpr.1.tensor_smooth hpr.1.tensor_symmetric hpr.2
      rwa [hyx] at h
end
end CKSLorentz

end






































end OAI
end

theorem solution.{u_1} : type_of% @OAI.CKSLorentz.actual_same_end_DEC.{u_1} := @OAI.CKSLorentz.actual_same_end_DEC.{u_1}
