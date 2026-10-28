-- Prove2me | solution 1 for OAI.ElasticityPhysicalEstimate.physical_compact_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:39:40.481364+00:00
-- url     : https://prove2.me/submissions/bccee361-d256-449c-b007-1eadd244be1e

import Mathlib
import Definitions.Def_OAIQ6El006

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma coord_coord (f : Smooth) (i j : Fin 3) (x : X) :
    (coord i (coord j f) : X → ℂ) x = fderiv ℝ (fderiv ℝ (f : X → ℂ)) x (e i) (e j) := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y (e j)) x (e i) = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (e j))]
  simp

lemma coord_commute (i j : Fin 3) (f : Smooth) : coord i (coord j f) = coord j (coord i f) := by
  apply Subtype.ext
  funext x
  rw [coord_coord, coord_coord]
  exact (smooth_coe f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

end DifferentialAlgebra

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

include hT in
lemma covariant_div_lap (u : ι → A) : divT T (fun i => lapT T (u i)) = lapT T (divT T u) := by
  simp only [divT, lapT, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hT i j, hT i j]

include hD hT hTD in
lemma covariant_div_cm (m : A) (u : ι → A) :
    divT T (cmT D T m u) =
    2*(∑ i, ∑ j, D i (D j m)*T i (u j)) +
      (∑ i, D i m*T i (divT T u)) + (∑ i, D i m*lapT T (u i)) := by
  have hH : (∑ i, ∑ j, D i (D j m)*T j (u i)) =
      ∑ i, ∑ j, D i (D j m)*T i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hD j i]
  have hv : (∑ i, ∑ j, D j m * T i (T j (u i))) =
      ∑ j, D j m*T j (divT T u) := by
    rw [Finset.sum_comm]
    simp only [divT, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hT i j]
  have hl : (∑ i, ∑ j, D j m * T i (T i (u j))) =
      ∑ j, D j m*lapT T (u j) := by
    rw [Finset.sum_comm]
    simp only [lapT, Finset.mul_sum]
  simp only [divT, cmT, map_sum, hTD, map_add, mul_add, Finset.sum_add_distrib]
  rw [hH, hv, hl]
  simp only [divT, map_sum]
  ring

include hD hT hTD in
/-- Compatibility after conjugation, proved for the genuine connection
Leibniz rule rather than falsely treating a shifted derivative as a derivation. -/
theorem covariant_augmented_identity (lam m : A) (u : ι → A) (d : A) :
    divT T (RT D T lam m u d) - ST D T lam m u d = PT D T m (divT T u-d) := by
  have hL := covariant_div_lap T hT u
  have hC := covariant_div_cm D T hD hT hTD m u
  simp only [divT] at hL hC
  simp only [divT, RT, map_add, hTD, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hL, hC]
  simp only [ST, PT, lap, lapT, map_sub, map_add, map_sum, mul_sub, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

include hT hTD in
lemma physical_conjugated_expansion (lam m : A) (u : ι → A) (i : ι) :
    LT T lam m u i = RT D T lam m u (divT T u) i := by
  have ht : (∑ j, T j (T i (u j))) = T i (divT T u) := by
    simp only [divT, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  simp only [LT, RT, hTD, map_add, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ht]
  simp only [cmT, lapT, mul_add, Finset.sum_add_distrib]
  ring

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

omit [Fintype ι] in
lemma shifted_mul (z : ι → ℂ) (i : ι) (a b : A) :
    shifted D z i (a*b) = D i a*b+a*shifted D z i b := by
  simp only [shifted_apply, partial_mul, Algebra.smul_def]
  ring

include hD in
omit [Fintype ι] in
lemma shifted_commute (z : ι → ℂ) (i j : ι) (f : A) :
    shifted D z i (shifted D z j f) = shifted D z j (shifted D z i f) := by
  simp only [shifted_apply, map_add, map_smul, smul_add, smul_smul, hD i j]
  simp only [Algebra.smul_def]
  ring_nf

theorem shifted_physical_expansion (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) (i : ι) :
    LT (shifted D z) lam m u i = RT D (shifted D z) lam m u (divT (shifted D z) u) i :=
  physical_conjugated_expansion D (shifted D z) (shifted_commute D hc z) (shifted_mul D z) lam m u i

theorem shifted_physical_divergence (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) :
    divT (shifted D z) (LT (shifted D z) lam m u) =
      ST D (shifted D z) lam m u (divT (shifted D z) u) := by
  have he := covariant_augmented_identity D (shifted D z) hc (shifted_commute D hc z)
    (shifted_mul D z) lam m u (divT (shifted D z) u)
  rw [sub_self] at he
  simp only [PT, lapT, map_zero, mul_zero, Finset.sum_const_zero, add_zero] at he
  rw [← sub_eq_zero]
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  funext i
  exact shifted_physical_expansion D z lam m u hc i

end CovariantAlgebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

lemma grad_cm (m : A) (u : ι → A) :
    (∑ i, D i m*cmT D T m u i) =
      2*(∑ i, ∑ j, D i m*D j m*T i (u j)) := by
  have hs : (∑ i, ∑ j, D i m*D j m*T j (u i)) =
      ∑ i, ∑ j, D i m*D j m*T i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [cmT, Finset.mul_sum, mul_add, ← mul_assoc, Finset.sum_add_distrib]
  rw [hs]
  ring_nf
  simp only [← Finset.sum_mul]

lemma grad_RT (lam m : A) (u : ι → A) (d : A) :
    (∑ i, D i m*RT D T lam m u d i) =
      m*(∑ i, D i m*lapT T (u i)) +
      (lam+m)*(∑ i, D i m*T i d) +
      2*(∑ i, ∑ j, D i m*D j m*T i (u j)) +
      (∑ i, D i m*D i lam)*d := by
  have hc := grad_cm D T m u
  simp only [RT, mul_add, Finset.sum_add_distrib]
  rw [hc]
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma normalized_vector (lam m n : A) (hn : n*m=1) (u : ι → A) (d : A) (i : ι) :
    n*RT D T lam m u d i = lapT T (u i) + ((lam+m)*n)*T i d +
      (∑ j, ((n*D j m)*T j (u i) + (n*D j m)*T i (u j))) +
      (n*D i lam)*d := by
  simp only [RT, cmT, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← mul_assoc]
  linear_combination lapT T (u i)*hn

lemma normalized_scalar_numerator (lam m n : A) (hn : n*m=1)
    (u : ι → A) (d : A) :
    ST D T lam m u d - 2*n*(∑ i, D i m*RT D T lam m u d i) =
      (lam+m+m)*lapT T d +
      2*(∑ i, (D i (lam+m)-(lam+m)*n*D i m)*T i d) +
      2*(∑ i, ∑ j, (D i (D j m)-2*n*D i m*D j m)*T i (u j)) +
      (lap D lam-2*n*(∑ i, D i m*D i lam))*d := by
  rw [grad_RT]
  simp only [ST, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_assoc, ← Finset.mul_sum]
  linear_combination -2*(∑ i, D i m*lapT T (u i))*hn

lemma normalized_scalar (lam m n o : A) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (u : ι → A) (d : A) :
    o*(ST D T lam m u d - 2*n*(∑ i, D i m*RT D T lam m u d i)) =
      lapT T d +
      (∑ i, (2*o*(D i (lam+m)-(lam+m)*n*D i m))*T i d) +
      (∑ i, ∑ j, (2*o*(D i (D j m)-2*n*D i m*D j m))*T i (u j)) +
      (o*(lap D lam-2*n*(∑ i, D i m*D i lam)))*d := by
  rw [normalized_scalar_numerator D T lam m n hn]
  simp only [mul_add, Finset.mul_sum, ← mul_assoc, ho, one_mul]
  ring_nf

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityBessel

lemma weight_pos (h s : ℝ) (x : X) : 0 < weight h s x := by
  exact Real.rpow_pos_of_pos (by positivity) _

lemma temperate_weight (h s : ℝ) : (weight h s).HasTemperateGrowth := by
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow X (s/2)).comp
    (((2*Real.pi*h) • ContinuousLinearMap.id ℝ X).hasTemperateGrowth)

lemma temperate_complex_weight (h s : ℝ) :
    (fun x => (weight h s x : ℂ)).HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (temperate_weight h s)

lemma weight_add (h s t : ℝ) (x : X) : weight h (s+t) x = weight h s x * weight h t x := by
  simp only [weight, add_div]
  exact Real.rpow_add (by positivity) _ _

lemma weight_neg (h s : ℝ) (x : X) : weight h (-s) x = (weight h s x)⁻¹ := by
  simp only [weight, neg_div]
  exact Real.rpow_neg (by positivity) _

@[simp] lemma M_apply (h s : ℝ) (f : S) (x : X) :
    M h s f x = (weight h s x : ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (temperate_complex_weight h s) f x

lemma M_add (h s t : ℝ) (f : S) : M h (s+t) f = M h s (M h t f) := by
  ext x
  simp only [M_apply, weight_add, Complex.ofReal_mul]
  ring

@[simp] lemma M_zero (h : ℝ) (f : S) : M h 0 f = f := by
  ext x
  simp only [M_apply, weight_zero, Complex.ofReal_one, one_mul]

lemma fourier_J (h s : ℝ) (f : S) : 𝓕 (J h s f) = M h s (𝓕 f) := by
  simp only [J, FourierTransform.fourier_fourierInv_eq]

lemma J_add_order (h s t : ℝ) (f : S) : J h (s+t) f = J h s (J h t f) := by
  simp only [J, FourierTransform.fourier_fourierInv_eq, M_add]

@[simp] lemma J_zero (h : ℝ) (f : S) : J h 0 f = f := by
  simp only [J, M_zero, FourierTransform.fourierInv_fourier_eq]

lemma J_add (h s : ℝ) (f g : S) : J h s (f+g) = J h s f + J h s g := by
  simp only [J, FourierTransform.fourier_add, map_add, FourierTransform.fourierInv_add]

lemma J_smul (h s : ℝ) (a : ℂ) (f : S) : J h s (a • f) = a • J h s f := by
  simp only [J, FourierTransform.fourier_smul, map_smul, FourierTransform.fourierInv_smul]

lemma J_deriv (h s : ℝ) (f : S) (v : X) : J h s (∂_{v} f) = ∂_{v} (J h s f) := by
  apply (FourierTransform.fourierCLE ℂ S).injective
  simp only [FourierTransform.fourierCLE_apply, fourier_J,
    SchwartzMap.fourier_lineDerivOp_eq]
  ext x
  have ht : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [map_smul, smul_apply, M_apply,
    SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul, Complex.real_smul]
  ring

lemma norm2_nonneg (f : S) : 0 ≤ norm2 f := norm_nonneg _

lemma norm2_add_le (f g : S) : norm2 (f+g) ≤ norm2 f + norm2 g := by
  simpa only [norm2, map_add] using norm_add_le (L2 f) (L2 g)

lemma norm2_const_smul (a : ℂ) (f : S) : norm2 (a • f) = ‖a‖*norm2 f := by
  simp only [norm2, map_smul, norm_smul]

lemma norm2_bound (f g : S) (c : ℝ) (h : ∀ x : X, ‖f x‖ ≤ c*‖g x‖) :
    norm2 f ≤ c*norm2 g := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
  change ‖f.toLp 2 volume x‖ ≤ c * ‖g.toLp 2 volume x‖
  rw [hx, hy]
  exact h x

lemma norm2_fourier (f : S) : norm2 (𝓕 f) = norm2 f :=
  SchwartzMap.norm_fourier_toL2_eq f

lemma norm2_fourierInv (f : S) : norm2 (𝓕⁻ f) = norm2 f := by
  have h := norm2_fourier (𝓕⁻ f)
  rw [FourierTransform.fourier_fourierInv_eq] at h
  exact h.symm

lemma norm2_J (h s : ℝ) (f : S) : norm2 (J h s f) = norm2 (M h s (𝓕 f)) :=
  norm2_fourierInv _

lemma real_weight_bound (h s t c : ℝ)
    (hw : ∀ x : X, weight h s x ≤ c*weight h t x) (f : S) :
    norm2 (J h s f) ≤ c*norm2 (J h t f) := by
  rw [norm2_J, norm2_J]
  apply norm2_bound
  intro x
  simp only [M_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos _ _ _)]
  exact (mul_le_mul_of_nonneg_right (hw x) (norm_nonneg (𝓕 f x))).trans_eq (by ring)

lemma fderiv_weight (h s : ℝ) (x v : X) :
    fderiv ℝ (weight h s) x v =
      s * (2*Real.pi*h)^2 * inner ℝ x v * weight h (s-2) x := by
  let c : ℝ := 2*Real.pi*h
  let L : X →L[ℝ] X := c • ContinuousLinearMap.id ℝ X
  have hn : HasFDerivAt (fun y : X => 1 + ‖c • y‖^2)
      (2 • (innerSL ℝ (c • x)).comp L) x := by
    simpa only [L, smul_apply, ContinuousLinearMap.id_apply] using
      (L.hasFDerivAt.norm_sq.const_add 1)
  have hp : (1 + ‖c • x‖^2) ≠ 0 := by positivity
  have hd := (hn.rpow_const (p := s/2) (Or.inl hp)).fderiv
  have he : s/2-1 = (s-2)/2 := by ring
  change fderiv ℝ (fun y : X => (1 + ‖c • y‖^2)^(s/2)) x v = _
  rw [hd]
  simp only [smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, L,
    ContinuousLinearMap.id_apply, real_inner_smul_left, real_inner_smul_right, he]
  change _ = s * c^2 * inner ℝ x v * (1+‖c • x‖^2)^((s-2)/2)
  ring

lemma fderiv_complex_weight (h s : ℝ) (x v : X) :
    fderiv ℝ (fun y => (weight h s y : ℂ)) x v =
      (s * (2*Real.pi*h)^2 * inner ℝ x v * weight h (s-2) x : ℝ) := by
  have hw := (temperate_weight h s).1.differentiable (by simp)
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x (hw x).hasFDerivAt).fderiv
  calc
    _ = (fderiv ℝ (weight h s) x v : ℂ) :=
      congrArg (fun T : X →L[ℝ] ℂ => T v) hd
    _ = _ := congrArg Complex.ofReal (fderiv_weight h s x v)

lemma Q_real (v : X) (f : S) :
    Q v f = SchwartzMap.smulLeftCLM ℂ (inner ℝ · v) f := by
  exact SchwartzMap.smulLeftCLM_ofReal ℂ (((innerSL ℝ).flip v).hasTemperateGrowth) f

lemma deriv_M (h s : ℝ) (v : X) (f : S) :
    ∂_{v} (M h s f) = M h s (∂_{v} f) +
      (s*(2*Real.pi*h)^2 : ℂ) • Q v (M h (s-2) f) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hc : (M h s f : X → ℂ) = fun y => (weight h s y : ℂ) * f y := by
    funext y
    exact M_apply h s f y
  rw [hc]
  change fderiv ℝ ((fun y => (weight h s y : ℂ)) * (f : X → ℂ)) x v = _
  rw [fderiv_mul ((temperate_complex_weight h s).1.differentiable (by simp) x)
    (f.differentiable x)]
  simp only [add_apply, smul_apply, smul_eq_mul,
    fderiv_complex_weight, M_apply, Q_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.ofReal_mul]
  push_cast
  ring

lemma fourier_Q (v : X) (f : S) :
    𝓕 (Q v f) = (-(2*Real.pi*Complex.I))⁻¹ • ∂_{v} (𝓕 f) := by
  have hn : (-(2*Real.pi*Complex.I) : ℂ) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, Complex.ofReal_eq_zero,
      OfNat.ofNat_ne_zero, Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  rw [SchwartzMap.lineDerivOp_fourier_eq, FourierTransform.fourier_smul, smul_smul]
  simp only [inv_mul_cancel₀ hn, one_smul, Q_real]

lemma Q_J (h s : ℝ) (v : X) (f : S) :
    Q v (J h s f) = J h s (Q v f) +
      (s*h^2 : ℂ) • J h (s-2) (∂_{v} f) := by
  apply (FourierTransform.fourierCLE ℂ S).injective
  simp only [FourierTransform.fourierCLE_apply, FourierTransform.fourier_add,
    FourierTransform.fourier_smul, fourier_Q, fourier_J, deriv_M,
    SchwartzMap.fourier_lineDerivOp_eq]
  ext x
  have ht : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [M_apply, Q_apply, smul_apply, add_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply ht, Complex.real_smul]
  field_simp
  simp only [Complex.I_sq]
  ring

lemma ip_integral (f g : S) : ip f g = ∫ x : X, star (f x) * g x := by
  simpa only [ip, L2, SchwartzMap.toLpCLM_apply, RCLike.inner_apply', RCLike.star_def]
    using SchwartzMap.inner_toL2_toL2_eq f g volume

lemma norm2_sq (f : S) : norm2 f ^ 2 = (ip f f).re := by
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (L2 f)).symm

lemma ip_fourier (f g : S) : ip (𝓕 f) (𝓕 g) = ip f g :=
  SchwartzMap.inner_fourier_toL2_eq f g

lemma ip_M (h s : ℝ) (f g : S) : ip (M h s f) g = ip f (M h s g) := by
  simp only [ip_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [M_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma ip_J (h s : ℝ) (f g : S) : ip (J h s f) g = ip f (J h s g) := by
  rw [← ip_fourier (J h s f) g, ← ip_fourier f (J h s g), fourier_J, fourier_J]
  exact ip_M h s _ _

lemma norm2_J_sq (h s : ℝ) (f : S) :
    norm2 (J h s f)^2 = (ip f (J h (s+s) f)).re := by
  rw [norm2_sq, ip_J, ← J_add_order]

lemma weight_one_sq (h : ℝ) (x : X) :
    weight h 1 x ^ 2 = 1 + ‖(2*Real.pi*h) • x‖^2 := by
  rw [sq, ← weight_add, show (1 : ℝ)+1=2 by norm_num, weight_two]

lemma norm_le_weight_one (h : ℝ) (x : X) :
    ‖(2*Real.pi*h) • x‖ ≤ weight h 1 x := by
  have hp := (weight_pos h 1 x).le
  have he := weight_one_sq h x
  nlinarith [norm_nonneg ((2*Real.pi*h) • x)]

lemma weight_mono (h : ℝ) {s t : ℝ} (hst : s ≤ t) (x : X) :
    weight h s x ≤ weight h t x := by
  exact Real.rpow_le_rpow_of_exponent_le
    (by nlinarith [sq_nonneg ‖(2*Real.pi*h) • x‖]) (by linarith)

lemma norm2_J_mono (h : ℝ) {s t : ℝ} (hst : s ≤ t) (f : S) :
    norm2 (J h s f) ≤ norm2 (J h t f) := by
  have he := real_weight_bound h s t 1 (fun x => by
    simpa only [one_mul] using weight_mono h hst x) f
  simpa only [one_mul] using he

lemma norm2_J_nonpos (h s : ℝ) (hs : s ≤ 0) (f : S) :
    norm2 (J h s f) ≤ norm2 f := by
  simpa only [J_zero] using norm2_J_mono h hs f

lemma norm_fourier_deriv (v : X) (f : S) (x : X) :
    ‖𝓕 (∂_{v} f) x‖ = (2*Real.pi) * |inner ℝ x v| * ‖𝓕 f x‖ := by
  have ht : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp only [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, abs_of_pos Real.pi_pos]
  ring

lemma semiclassical_frequency_bound (h : ℝ) (x v : X) :
    |h| * (2*Real.pi) * |inner ℝ x v| ≤ weight h 1 x * ‖v‖ := by
  have hi := abs_real_inner_le_norm x v
  have hn := norm_le_weight_one h x
  have hc : ‖(2*Real.pi*h) • x‖ = |h| *(2*Real.pi)*‖x‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    ring
  rw [hc] at hn
  calc
    |h| *(2*Real.pi)*|inner ℝ x v| ≤ |h| *(2*Real.pi)*(‖x‖*‖v‖) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (|h| *(2*Real.pi)*‖x‖)*‖v‖ := by ring
    _ ≤ weight h 1 x * ‖v‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)

lemma norm2_J_semideriv (h s : ℝ) (v : X) (f : S) :
    norm2 ((h : ℂ) • J h (s-1) (∂_{v} f)) ≤ ‖v‖ * norm2 (J h s f) := by
  rw [← norm2_fourier ((h : ℂ) • J h (s-1) (∂_{v} f)),
    FourierTransform.fourier_smul, fourier_J, norm2_J]
  apply norm2_bound
  intro x
  simp only [smul_apply, M_apply, norm_smul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos _ _ _),
    norm_fourier_deriv]
  have hi := semiclassical_frequency_bound h x v
  have hw : weight h (s-1) x * weight h 1 x = weight h s x := by
    rw [← weight_add]
    congr 1
    ring
  calc
    |h| * (weight h (s-1) x * ((2*Real.pi)*|inner ℝ x v| *‖𝓕 f x‖)) =
        weight h (s-1) x * (|h| *(2*Real.pi)*|inner ℝ x v|) * ‖𝓕 f x‖ := by ring
    _ ≤ weight h (s-1) x * (weight h 1 x * ‖v‖) * ‖𝓕 f x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (weight_pos _ _ _).le) (norm_nonneg _)
    _ = ‖v‖ * (weight h s x * ‖𝓕 f x‖) := by rw [← hw]; ring

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticitySchwartzCarleman

lemma smooth (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) := f.smooth _

lemma d_d (v w : X) (f : Test) (z : X) :
    (d v (d w f) : X → ℂ) z = fderiv ℝ (fderiv ℝ (f : X → ℂ)) z v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y w) z v = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
  simp

lemma d_comm (v w : X) (f : Test) : d v (d w f) = d w (d v f) := by
  ext z
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

lemma deriv_conj (f : Test) (z v : X) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : X → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : X →L[ℝ] ℂ => L v) h

lemma integrable_pair (f g : Test) : Integrable (fun z : X => star (f z)*g z) := by
  have hi := (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
    (f.postcompCLM Complex.conjCLE.toContinuousLinearMap) g).integrable (μ := volume)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rfl

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, FunLike.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_add_left (f g h : Test) : pair (f+g) h = pair f h + pair g h := by
  simpa only [pair, FunLike.coe_add, Pi.add_apply, star_add, add_mul] using
    integral_add (integrable_pair f h) (integrable_pair g h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, FunLike.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_left (f g h : Test) : pair (f-g) h = pair f h - pair g h := by
  simpa only [pair, FunLike.coe_sub, Pi.sub_apply, star_sub, sub_mul] using
    integral_sub (integrable_pair f h) (integrable_pair g h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_smul_left (f g : Test) (a : ℂ) : pair (a • f) g = star a * pair f g := by
  simp only [pair, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul, mul_comm (star (f _)), mul_assoc]
  exact integral_const_mul (star a) _

/-- Coordinate derivatives are skew adjoint on the actual test space. -/
lemma pair_real_smul_left (f g : Test) (a : ℝ) :
    pair (a • f) g = (a : ℂ) * pair f g := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a, pair_smul_left]
  simp

lemma pair_d (f g : Test) (v : X) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : X => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : X => star (f z)*fderiv ℝ (g : X → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma mass_integral (f : Test) : mass f = ∫ z : X, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma integrable_normSq (f : Test) : Integrable (fun z : X => Complex.normSq (f z)) := by
  have h := (integrable_pair f f).re
  simpa only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

lemma d_Q (v : X) (f : Test) : d v (Q f) = (qCLM v) • f + Q (d v f) := by
  ext x
  rw [d_apply]
  have hc : (Q f : X → ℂ) = fun x => qCLM x * f x := by
    funext x
    exact Q_apply f x
  rw [hc]
  simp only [add_apply, smul_apply, smul_eq_mul, Q_apply]
  change fderiv ℝ (fun x => qCLM x * f x) x v = qCLM v * f x + qCLM x * ((d v f : X → ℂ) x)
  have h := congrArg (fun L : X →L[ℝ] ℂ => L v)
    ((qCLM.hasFDerivAt (x := x)).mul ((smooth f).differentiable (by simp) x).hasFDerivAt).fderiv
  simpa [d_apply, add_comm, mul_comm, Pi.mul_def] using h

lemma pair_Q (f g : Test) : pair f (Q g) = pair (Q f) g := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [Q_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma lap_apply (f : Test) : lap f = d (e 0) (d (e 0) f) +
    d (e 1) (d (e 1) f) + d (e 2) (d (e 2) f) := by
  simp [lap, Fin.sum_univ_three]

lemma d_G (v : X) (a b : ℝ) (f : Test) :
    d v (G a b f) = ((b : ℂ) * qCLM v) • f + G a b (d v f) := by
  simp only [G, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_add, map_smul, d_Q]
  module

lemma pair_G (a b : ℝ) (f g : Test) : pair f (G a b g) = pair (G a b f) g := by
  simp only [G, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    pair_add_right, pair_smul_right, pair_add_left, pair_smul_left, pair_Q,
    Complex.star_def, Complex.conj_ofReal]

lemma lap_comm (v : X) (f : Test) : lap (d v f) = d v (lap f) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [d_comm (e i) v f, d_comm (e i) v (d (e i) f)]

lemma lap_G (a b : ℝ) (f : Test) :
    lap (G a b f) = (2 * (b : ℂ)) • d (e 0) f + G a b (lap f) := by
  simp only [lap_apply, d_G, map_add, map_smul, qCLM_e]
  norm_num [show (2 : Fin 3) ≠ 0 by decide]
  module

lemma pair_dd (v : X) (f g : Test) :
    pair f (d v (d v g)) = pair (d v (d v f)) g := by
  rw [pair_d, pair_d, neg_neg]

lemma pair_lap (f g : Test) : pair f (lap g) = pair (lap f) g := by
  simp only [lap_apply, pair_add_right, pair_add_left, pair_dd]

lemma pair_A (h a b : ℝ) (f g : Test) : pair f (A h a b g) = pair (A h a b f) g := by
  simp only [A, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    pair_sub_right, pair_sub_left, pair_smul_right, pair_smul_left,
    map_neg, map_pow, Complex.star_def, Complex.conj_ofReal]
  rw [pair_lap, pair_G, pair_G]

lemma pair_B (h a b : ℝ) (f g : Test) : pair f (B h a b g) = -pair (B h a b f) g := by
  simp only [B, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.id_apply, pair_add_right, pair_add_left, pair_smul_right,
    pair_smul_left, map_mul, Complex.star_def, Complex.conj_ofReal,
    map_ofNat]
  rw [pair_G, pair_d, d_G]
  norm_num [pair_add_left, pair_smul_left, pair_real_smul_left, e]
  ring

/-- The commutator producing the convexification gain. -/
lemma commutator (h a b : ℝ) (f : Test) :
    A h a b (B h a b f) - B h a b (A h a b f) =
      (-4 * (h : ℂ)^3 * b) • d (e 0) (d (e 0) f) +
      (4 * (h : ℂ) * b) • G a b (G a b f) := by
  simp only [A, B, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.id_apply, map_add, map_sub, map_smul,
    lap_G, lap_comm, d_G, qCLM_e]
  norm_num
  module

lemma energy_identity (h a b : ℝ) (f : Test) :
    mass (P h a b f) = mass (A h a b f) + mass (B h a b f) +
      4 * h^3 * b * mass (d (e 0) f) + 4 * h * b * mass (G a b f) := by
  have hc : pair (A h a b f) (B h a b f) + pair (B h a b f) (A h a b f) =
      (-4 * (h : ℂ)^3 * b) * pair f (d (e 0) (d (e 0) f)) +
      (4 * (h : ℂ) * b) * pair f (G a b (G a b f)) := by
    calc
      _ = pair f (A h a b (B h a b f) - B h a b (A h a b f)) := by
        rw [pair_sub_right, pair_A h a b f (B h a b f), pair_B h a b f (A h a b f)]
        ring
      _ = _ := by rw [commutator, pair_add_right, pair_smul_right, pair_smul_right]
  rw [pair_d, pair_G] at hc
  have hp : pair (P h a b f) (P h a b f) =
      pair (A h a b f) (A h a b f) + pair (B h a b f) (B h a b f) +
      ((4 * h^3 * b : ℝ) : ℂ) * pair (d (e 0) f) (d (e 0) f) +
      ((4 * h * b : ℝ) : ℂ) * pair (G a b f) (G a b f) := by
    simp only [P, LinearMap.add_apply, pair_add_right, pair_add_left]
    push_cast
    linear_combination hc
  have hr := congrArg Complex.re hp
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  exact hr

lemma mass_A_le (h a b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (f : Test) :
    mass (A h a b f) ≤ mass (P h a b f) := by
  rw [energy_identity]
  have h₁ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
    (pow_nonneg hh 3)) hb) (mass_nonneg (d (e 0) f))
  have h₂ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
    hh) hb) (mass_nonneg (G a b f))
  linarith [mass_nonneg (B h a b f)]

lemma mass_G_le (h a b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (f : Test) :
    4*h*b*mass (G a b f) ≤ mass (P h a b f) := by
  rw [energy_identity]
  have h₁ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4)
    (pow_nonneg hh 3)) hb) (mass_nonneg (d (e 0) f))
  linarith [mass_nonneg (A h a b f), mass_nonneg (B h a b f)]

lemma pair_symm (f g : Test) : star (pair f g) = pair g f := by
  simp only [pair, Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul, Complex.conj_conj]
  ring

lemma pair_re_bound (f g : Test) :
    2 * (pair f g).re ≤ mass f + mass g := by
  have hm := mass_nonneg (f-g)
  simp only [mass, pair_sub_left, pair_sub_right, Complex.sub_re] at hm
  have he := congrArg Complex.re (pair_symm f g)
  simp only [Complex.star_def, Complex.conj_re] at he
  change 2 * _ ≤ (pair f f).re + (pair g g).re
  linarith

lemma gradientMass_nonneg (f : Test) : 0 ≤ gradientMass f :=
  Finset.sum_nonneg fun _ _ => mass_nonneg _

lemma lap_energy (f : Test) : (pair f (lap f)).re = -gradientMass f := by
  simp only [gradientMass, lap_apply, Fin.sum_univ_three, pair_add_right,
    pair_d, Complex.add_re, Complex.neg_re, mass]
  ring

lemma kinetic_identity (h a b : ℝ) (f : Test) :
    h^2 * gradientMass f = (pair f (A h a b f)).re + mass (G a b f) := by
  simp only [A, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    pair_sub_right, pair_smul_right, Complex.sub_re]
  rw [pair_G]
  have hc : -(h : ℂ)^2 = ((-h^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    lap_energy]
  dsimp [mass]
  ring

lemma mass_add_bound (f g : Test) : mass (f+g) ≤ 2*mass f+2*mass g := by
  have hp := pair_re_bound f g
  have he := congrArg Complex.re (pair_symm f g)
  simp only [Complex.star_def, Complex.conj_re] at he
  simp only [mass, pair_add_left, pair_add_right, Complex.add_re]
  dsimp [mass] at hp
  linarith

lemma mass_ofReal_smul (a : ℝ) (f : Test) : mass ((a : ℂ) • f) = a^2*mass f := by
  simp only [mass, pair_smul_left, pair_smul_right, Complex.star_def,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

lemma mass_neg (f : Test) : mass (-f) = mass f := by
  have he := mass_ofReal_smul (-1) f
  simpa using he

lemma affine_mass_bounds (b : ℝ) (f : Test) :
    mass f ≤ 2*mass (G (-1) b f) + 2*b^2*mass (Q f) ∧
    mass (G (-1) b f) ≤ 2*mass f + 2*b^2*mass (Q f) := by
  have he : f = -G (-1) b f + (b : ℂ) • Q f := by
    simp only [G, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    push_cast
    module
  have ht : G (-1) b f = -f + (b : ℂ) • Q f := by
    simp only [G, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    push_cast
    module
  constructor
  · have hm := mass_add_bound (-G (-1) b f) ((b : ℂ) • Q f)
    rw [← he, mass_neg, mass_ofReal_smul] at hm
    nlinarith
  · rw [ht]
    have hm := mass_add_bound (-f) ((b : ℂ) • Q f)
    rw [mass_neg, mass_ofReal_smul] at hm
    nlinarith

lemma affine_square_mass_bound (b : ℝ) (f : Test) :
    mass (G (-1) b (G (-1) b f)) ≤
      4*mass f+16*b^2*mass (Q f)+4*b^4*mass (Q (Q f)) := by
  have hm := (affine_mass_bounds b (G (-1) b f)).2
  have hq : Q (G (-1) b f) = G (-1) b (Q f) := by
    simp only [G, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_add, map_smul]
  rw [hq] at hm
  have hu := (affine_mass_bounds b f).2
  have hv := (affine_mass_bounds b (Q f)).2
  have he := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2*b^2)
  nlinarith [mul_nonneg (sq_nonneg b) (mass_nonneg (Q f))]

/-- Schwartz Carleman algebra with controlled moments, without a false
compact-support claim for Bessel potentials. -/
lemma scalar_H2_moment_bound (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hsmall : h*b ≤ 1) (f : Test) :
    h*b*(mass f+2*h^2*gradientMass f+h^4*mass (lap f)) ≤
      10*mass (P h (-1) b f) +
        h*b*(64*b^2*mass (Q f)+8*b^4*mass (Q (Q f))) := by
  have hs := (affine_mass_bounds b f).1
  have hu := (affine_mass_bounds b f).2
  have hG := mass_G_le h (-1) b hh hb f
  have hA := mass_A_le h (-1) b hh hb f
  have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg hh hb)
  have hm : h*b*mass f ≤ (1/2:ℝ)*mass (P h (-1) b f) +
      2*h*b^3*mass (Q f) := by nlinarith
  have hk := kinetic_identity h (-1) b f
  have hp := pair_re_bound f (A h (-1) b f)
  have hg : h^2*gradientMass f ≤ (1/2:ℝ)*mass (P h (-1) b f)+
      (5/2:ℝ)*mass f+2*b^2*mass (Q f) := by linarith
  have he : ((-h^2 : ℝ) : ℂ) • lap f =
      A h (-1) b f + G (-1) b (G (-1) b f) := by
    simp only [A, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    push_cast
    module
  have hl := mass_add_bound (A h (-1) b f) (G (-1) b (G (-1) b f))
  rw [← he, mass_ofReal_smul] at hl
  have hgg := affine_square_mass_bound b f
  have hlap : h^4*mass (lap f) ≤ 2*mass (P h (-1) b f)+
      8*mass f+32*b^2*mass (Q f)+8*b^4*mass (Q (Q f)) := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hg (mul_nonneg hh hb)
  have h₂ := mul_le_mul_of_nonneg_left hlap (mul_nonneg hh hb)
  have h₃ := mul_le_mul_of_nonneg_right hsmall (mass_nonneg (P h (-1) b f))
  nlinarith

end ElasticitySchwartzCarleman

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma norm2_sq_mass (f : S) : norm2 f^2 = mass f := by
  rw [norm2_sq, ip_integral]
  rfl

lemma Q_bridge (f : S) : ElasticityBessel.Q (e 0) f = ElasticitySchwartzCarleman.Q f := by
  ext x
  simp [ElasticityBessel.Q_apply, ElasticitySchwartzCarleman.Q_apply,
    e, EuclideanSpace.inner_single_right]

lemma fourier_d (i : Fin 3) (f : S) (x : X) :
    𝓕 (d (e i) f) x = (2*Real.pi*Complex.I)*(x i : ℂ)*𝓕 f x := by
  have ht : (inner ℝ · (e i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (e i)).hasTemperateGrowth
  change 𝓕 (∂_{e i} f) x = _
  simp only [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ht, Complex.real_smul, smul_eq_mul]
  simp only [e, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  ring

lemma J_two (h : ℝ) (f : S) : J h 2 f = f - (h : ℂ)^2 • lap f := by
  apply (FourierTransform.fourierCLE ℂ S).injective
  rw [map_sub, map_smul]
  simp only [FourierTransform.fourierCLE_apply, fourier_J, lap_apply,
    FourierTransform.fourier_add]
  ext x
  simp only [M_apply, weight_two, sub_apply, add_apply, smul_apply, smul_eq_mul,
    fourier_d, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    PiLp.smul_apply, smul_eq_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma mass_sub (f g : S) : mass (f-g) = mass f - 2*(pair f g).re + mass g := by
  have hs := congrArg Complex.re (pair_symm f g)
  simp only [Complex.star_def, Complex.conj_re] at hs
  simp only [mass, pair_sub_left, pair_sub_right, Complex.sub_re]
  linarith

lemma H2_energy (h : ℝ) (f : S) :
    norm2 (J h 2 f)^2 = mass f+2*h^2*gradientMass f+h^4*mass (lap f) := by
  rw [norm2_sq_mass, J_two, mass_sub]
  have hc : (h : ℂ)^2 = ((h^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, mass_ofReal_smul, pair_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, lap_energy]
  ring

lemma d_eq (v : X) (f : S) : d v f = ∂_{v} f := by
  ext x
  rfl

lemma semideriv_bound (h s : ℝ) (hh : 0 ≤ h) (i : Fin 3) (f : S) :
    h * norm2 (J h (s-1) (d (e i) f)) ≤ norm2 (J h s f) := by
  have ht := norm2_J_semideriv h s (e i) f
  rw [norm2_const_smul] at ht
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh,
    e, PiLp.norm_single, norm_one, one_mul, d_eq] using ht

lemma second_deriv_bound (h s : ℝ) (hh : 0 ≤ h) (i j : Fin 3) (f : S) :
    h^2 * norm2 (J h (s-2) (d (e i) (d (e j) f))) ≤ norm2 (J h s f) := by
  have h₁ := semideriv_bound h (s-1) hh i (d (e j) f)
  have h₂ := semideriv_bound h s hh j f
  rw [show s-1-1=s-2 by ring] at h₁
  have h₃ := mul_le_mul_of_nonneg_left h₁ hh
  nlinarith only [h₂, h₃]

lemma Q_J (h s : ℝ) (f : S) :
    ElasticitySchwartzCarleman.Q (J h s f) =
      J h s (ElasticitySchwartzCarleman.Q f) +
        ((s*h^2 : ℝ) : ℂ) • J h (s-2) (d (e 0) f) := by
  simpa only [Q_bridge, Complex.ofReal_mul, Complex.ofReal_pow, d_eq] using
    ElasticityBessel.Q_J h s (e 0) f

lemma QQ_J (h s : ℝ) (f : S) :
    ElasticitySchwartzCarleman.Q (ElasticitySchwartzCarleman.Q (J h s f)) =
      J h s (ElasticitySchwartzCarleman.Q (ElasticitySchwartzCarleman.Q f)) +
        ((2*s*h^2 : ℝ) : ℂ) • J h (s-2) (d (e 0) (ElasticitySchwartzCarleman.Q f)) -
        ((s*h^2 : ℝ) : ℂ) • J h (s-2) f +
        ((s*(s-2)*h^4 : ℝ) : ℂ) • J h (s-4) (d (e 0) (d (e 0) f)) := by
  rw [Q_J, map_add, map_smul, Q_J, Q_J]
  have hd : ElasticitySchwartzCarleman.Q (d (e 0) f) =
      d (e 0) (ElasticitySchwartzCarleman.Q f) - f := by
    rw [d_Q, qCLM_e]
    norm_num
  rw [hd]
  have hjsub (t : ℝ) (u v : S) : J h t (u-v) = J h t u - J h t v := by
    rw [sub_eq_add_neg, J_add, ← neg_one_smul ℂ v, J_smul]
    simp only [neg_one_smul, sub_eq_add_neg]
  rw [hjsub, show s-2-2=s-4 by ring]
  push_cast
  module

lemma norm2_real_smul (a : ℝ) (f : S) :
    norm2 ((a : ℂ) • f) = |a| * norm2 f := by
  rw [norm2_const_smul, Complex.norm_real, Real.norm_eq_abs]

lemma norm2_sub_le (f g : S) : norm2 (f-g) ≤ norm2 f+norm2 g := by
  simpa only [norm2, map_sub] using norm_sub_le (L2 f) (L2 g)

lemma norm2_Q_supported (R : ℝ) (_hR : 0 ≤ R) (f : S)
    (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (ElasticitySchwartzCarleman.Q f) ≤ R*norm2 f := by
  apply norm2_bound
  intro x
  rw [ElasticitySchwartzCarleman.Q_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hx : f x = 0
  · simp only [hx, norm_zero, mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right (hf x hx) (norm_nonneg _)

lemma norm2_QQ_supported (R : ℝ) (hR : 0 ≤ R) (f : S)
    (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (ElasticitySchwartzCarleman.Q (ElasticitySchwartzCarleman.Q f)) ≤ R^2*norm2 f := by
  have hs := norm2_Q_supported R hR (ElasticitySchwartzCarleman.Q f) (by
    intro x hx
    apply hf x
    intro hz
    exact hx (by simp [ElasticitySchwartzCarleman.Q_apply, hz]))
  have hs' := mul_le_mul_of_nonneg_left (norm2_Q_supported R hR f hf) hR
  nlinarith only [hs, hs']

local notation "Q₀" => ElasticitySchwartzCarleman.Q
local notation "D₀" => d (e 0)

lemma semideriv_nonpos (h s : ℝ) (hh : 0 ≤ h) (hs : s ≤ 0)
    (i : Fin 3) (f : S) :
    h*norm2 (J h (s-1) (d (e i) f)) ≤ norm2 f :=
  (semideriv_bound h s hh i f).trans (norm2_J_nonpos h s hs f)

lemma second_deriv_nonpos (h s : ℝ) (hh : 0 ≤ h) (hs : s ≤ 0)
    (i j : Fin 3) (f : S) :
    h^2*norm2 (J h (s-2) (d (e i) (d (e j) f))) ≤ norm2 f :=
  (second_deriv_bound h s hh i j f).trans (norm2_J_nonpos h s hs f)

lemma first_moment (h R : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hR : 1 ≤ R) (f : S)
    (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (Q₀ (J h (-1) f)) ≤ 2*R*norm2 f := by
  have he : Q₀ (J h (-1) f) = J h (-1) (Q₀ f) +
      ((-h^2 : ℝ) : ℂ) • J h (-3) (D₀ f) := by
    convert Q_J h (-1) f using 1; norm_num
  have ht := norm2_add_le (J h (-1) (Q₀ f))
    (((-h^2 : ℝ) : ℂ) • J h (-3) (D₀ f))
  rw [← he, norm2_real_smul, abs_neg, abs_of_nonneg (sq_nonneg h)] at ht
  have hA := norm2_J_nonpos h (-1) (by norm_num) (Q₀ f)
  have hB : h*norm2 (J h (-3) (D₀ f)) ≤ norm2 f := by
    convert semideriv_nonpos h (-2) hh (by norm_num) 0 f using 1; norm_num
  have hB' := mul_le_mul_of_nonneg_left hB hh
  have hQ := norm2_Q_supported R (by linarith) f hf
  have hn := norm2_nonneg f
  have hh' := mul_le_mul_of_nonneg_right hh1 hn
  have hR' := mul_le_mul_of_nonneg_right hR hn
  nlinarith only [ht, hA, hB', hQ, hh', hR']

lemma norm2_four_terms (a b c d : S) :
    norm2 (a+b-c+d) ≤ norm2 a+norm2 b+norm2 c+norm2 d := by
  have h₁ := norm2_add_le (a+b-c) d
  have h₂ := norm2_sub_le (a+b) c
  have h₃ := norm2_add_le a b
  linarith only [h₁, h₂, h₃]

lemma second_moment (h R : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hR : 1 ≤ R) (f : S)
    (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (Q₀ (Q₀ (J h (-1) f))) ≤ 7*R^2*norm2 f := by
  have he : Q₀ (Q₀ (J h (-1) f)) = J h (-1) (Q₀ (Q₀ f)) +
      ((-2*h^2 : ℝ) : ℂ) • J h (-3) (D₀ (Q₀ f)) -
      ((-h^2 : ℝ) : ℂ) • J h (-3) f +
      ((3*h^4 : ℝ) : ℂ) • J h (-5) (D₀ (D₀ f)) := by
    convert QQ_J h (-1) f using 1; norm_num
  have ht := norm2_four_terms (J h (-1) (Q₀ (Q₀ f)))
    (((-2*h^2 : ℝ) : ℂ) • J h (-3) (D₀ (Q₀ f)))
    (((-h^2 : ℝ) : ℂ) • J h (-3) f)
    (((3*h^4 : ℝ) : ℂ) • J h (-5) (D₀ (D₀ f)))
  rw [← he] at ht
  simp only [norm2_real_smul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg h),
    abs_of_nonneg (pow_nonneg hh 4)] at ht
  norm_num at ht
  have hA := norm2_J_nonpos h (-1) (by norm_num) (Q₀ (Q₀ f))
  have hD : h*norm2 (J h (-3) (D₀ (Q₀ f))) ≤ norm2 (Q₀ f) := by
    convert semideriv_nonpos h (-2) hh (by norm_num) 0 (Q₀ f) using 1; norm_num
  have hD' := mul_le_mul_of_nonneg_left hD hh
  have hhQ := mul_le_mul_of_nonneg_right hh1 (norm2_nonneg (Q₀ f))
  have hQ := norm2_Q_supported R (by linarith) f hf
  have hQQ := norm2_QQ_supported R (by linarith) f hf
  have hC := norm2_J_nonpos h (-3) (by norm_num) f
  have hC' := mul_le_mul_of_nonneg_left hC (sq_nonneg h)
  have hh2 : h^2 ≤ 1 := by nlinarith
  have hh2n := mul_le_mul_of_nonneg_right hh2 (norm2_nonneg f)
  have hDD : h^2*norm2 (J h (-5) (D₀ (D₀ f))) ≤ norm2 f := by
    convert second_deriv_nonpos h (-3) hh (by norm_num) 0 0 f using 1; norm_num
  have hDD' := mul_le_mul_of_nonneg_left hDD (sq_nonneg h)
  have hR2 : R^2+2*R+4 ≤ 7*R^2 := by nlinarith [sq_nonneg (R-1)]
  have hR2n := mul_le_mul_of_nonneg_right hR2 (norm2_nonneg f)
  nlinarith only [ht, hA, hD', hhQ, hQ, hQQ, hC', hh2n, hDD', hR2n]

lemma J_sub (h s : ℝ) (f g : S) : J h s (f-g) = J h s f-J h s g := by
  rw [sub_eq_add_neg, J_add, ← neg_one_smul ℂ g, J_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

lemma d_J (h s : ℝ) (v : X) (f : S) : d v (J h s f) = J h s (d v f) := by
  simp only [d_eq, J_deriv]

lemma lap_J (h s : ℝ) (f : S) : lap (J h s f) = J h s (lap f) := by
  simp only [lap_apply, J_add, d_J]

lemma P_expanded (h b : ℝ) (f : S) :
    P h (-1) b f = ((-h^2 : ℝ) : ℂ) • lap f - f +
      ((2*b : ℝ) : ℂ) • Q₀ f - ((b^2 : ℝ) : ℂ) • Q₀ (Q₀ f) -
      ((2*h : ℝ) : ℂ) • D₀ f + ((2*h*b : ℝ) : ℂ) • Q₀ (D₀ f) +
      ((h*b : ℝ) : ℂ) • f := by
  simp only [P, A, B, G, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add, map_smul]
  push_cast
  module

lemma P_shift (h b : ℝ) (f : S) :
    P h (-1) b (J h (-1) f) = J h (-1) (P h (-1) b f) +
      ((-2*b*h^2 : ℝ) : ℂ) • J h (-3) (D₀ f) +
      ((2*b^2*h^2 : ℝ) : ℂ) • J h (-3) (D₀ (Q₀ f)) -
      ((b^2*h^2 : ℝ) : ℂ) • J h (-3) f -
      ((3*b^2*h^4 : ℝ) : ℂ) • J h (-5) (D₀ (D₀ f)) -
      ((2*b*h^3 : ℝ) : ℂ) • J h (-3) (D₀ (D₀ f)) := by
  simp only [P_expanded, J_add, J_sub, J_smul, lap_J, d_J]
  rw [QQ_J]
  simp only [Q_J]
  norm_num
  module

lemma norm2_six_terms (a b c d e f : S) :
    norm2 (a+b+c-d-e-f) ≤ norm2 a+norm2 b+norm2 c+norm2 d+norm2 e+norm2 f := by
  have h₁ := norm2_sub_le (a+b+c-d-e) f
  have h₂ := norm2_sub_le (a+b+c-d) e
  have h₃ := norm2_sub_le (a+b+c) d
  have h₄ := norm2_add_le (a+b) c
  have h₅ := norm2_add_le a b
  linarith only [h₁, h₂, h₃, h₄, h₅]

lemma norm2_P_shift (h b R : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hbR : b*R ≤ 1) (hhb : h*b ≤ 1) (f : S)
    (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (P h (-1) b (J h (-1) f)) ≤
      norm2 (J h (-1) (P h (-1) b f)) + 10*h*b*norm2 f := by
  have ht := norm2_six_terms (J h (-1) (P h (-1) b f))
    (((-2*b*h^2 : ℝ) : ℂ) • J h (-3) (D₀ f))
    (((2*b^2*h^2 : ℝ) : ℂ) • J h (-3) (D₀ (Q₀ f)))
    (((b^2*h^2 : ℝ) : ℂ) • J h (-3) f)
    (((3*b^2*h^4 : ℝ) : ℂ) • J h (-5) (D₀ (D₀ f)))
    (((2*b*h^3 : ℝ) : ℂ) • J h (-3) (D₀ (D₀ f)))
  rw [← P_shift] at ht
  simp only [norm2_real_smul, abs_mul, abs_pow, abs_of_nonneg hh, abs_of_nonneg hb] at ht
  norm_num at ht
  have hD : h*norm2 (J h (-3) (D₀ f)) ≤ norm2 f := by
    convert semideriv_nonpos h (-2) hh (by norm_num) 0 f using 1; norm_num
  have hDQ : h*norm2 (J h (-3) (D₀ (Q₀ f))) ≤ norm2 (Q₀ f) := by
    convert semideriv_nonpos h (-2) hh (by norm_num) 0 (Q₀ f) using 1; norm_num
  have hQ := norm2_Q_supported R hR f hf
  have hC := norm2_J_nonpos h (-3) (by norm_num) f
  have hDD5 : h^2*norm2 (J h (-5) (D₀ (D₀ f))) ≤ norm2 f := by
    convert second_deriv_nonpos h (-3) hh (by norm_num) 0 0 f using 1; norm_num
  have hDD3 : h^2*norm2 (J h (-3) (D₀ (D₀ f))) ≤ norm2 f := by
    convert second_deriv_nonpos h (-1) hh (by norm_num) 0 0 f using 1; norm_num
  have hp : 0 ≤ h*b := mul_nonneg hh hb
  have hn := norm2_nonneg f
  have h₁ := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 2*h*b)
  have h₂ := mul_le_mul_of_nonneg_left (hDQ.trans hQ) (by positivity : 0 ≤ 2*b^2*h)
  have h₃ := mul_le_mul_of_nonneg_left hC (by positivity : 0 ≤ b^2*h^2)
  have h₄ := mul_le_mul_of_nonneg_left hDD5 (by positivity : 0 ≤ 3*b^2*h^2)
  have h₅ := mul_le_mul_of_nonneg_left hDD3 (by positivity : 0 ≤ 2*b*h)
  have hsmallR := mul_le_mul_of_nonneg_left hbR (by positivity : 0 ≤ 2*h*b*norm2 f)
  have hsmallh := mul_le_mul_of_nonneg_left hhb (mul_nonneg hp hn)
  nlinarith only [ht, h₁, h₂, h₃, h₄, h₅, hsmallR, hsmallh]

lemma moment_coefficient_small (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1/100) :
    256*z^2+392*z^4 ≤ (1/4 : ℝ) := by
  have h₂ := pow_le_pow_left₀ hz hz' 2
  have h₄ := pow_le_pow_left₀ hz hz' 4
  norm_num at h₂ h₄
  linarith only [h₂, h₄]

lemma norm2_J_one_ge (h : ℝ) (f : S) : norm2 f ≤ norm2 (J h 1 f) := by
  have ht := norm2_J_mono h (show (0 : ℝ) ≤ 1 by norm_num) f
  simpa only [J_zero] using ht

lemma shifted_energy (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (hhb : h*b ≤ 1)
    (f : S) :
    h*b*norm2 (J h 1 f)^2 ≤ 10*norm2 (P h (-1) b (J h (-1) f))^2 +
      h*b*(64*b^2*norm2 (Q₀ (J h (-1) f))^2 +
        8*b^4*norm2 (Q₀ (Q₀ (J h (-1) f)))^2) := by
  have ht := scalar_H2_moment_bound h b hh hb hhb (J h (-1) f)
  rw [← H2_energy h (J h (-1) f)] at ht
  have hj : J h 2 (J h (-1) f) = J h 1 f := by
    rw [← J_add_order]
    norm_num
  rw [hj] at ht
  simpa only [← norm2_sq_mass] using ht

/-- The missing scalar negative-order shift, obtained using actual nonlocal
Bessel potentials and Schwartz moments, not a false preservation of support. -/
lemma scalar_supported_shift (h b R : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hb : 0 ≤ b) (hR : 1 ≤ R) (hbR : b*R ≤ 1/100) (hhb : h*b ≤ 1/8000)
    (f : S) (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    h*b*norm2 (J h 1 f)^2 ≤ 40*norm2 (J h (-1) (P h (-1) b f))^2 := by
  have hR0 : 0 ≤ R := by linarith
  have hp : 0 ≤ h*b := mul_nonneg hh hb
  have hn := norm2_nonneg f
  have he := shifted_energy h b hh hb (by linarith) f
  have hq := first_moment h R hh hh1 hR f hf
  have hqq := second_moment h R hh hh1 hR f hf
  have hq₂ := pow_le_pow_left₀ (norm2_nonneg (Q₀ (J h (-1) f))) hq 2
  have hqq₂ := pow_le_pow_left₀ (norm2_nonneg (Q₀ (Q₀ (J h (-1) f)))) hqq 2
  have hq₃ := mul_le_mul_of_nonneg_left hq₂ (by positivity : 0 ≤ h*b*64*b^2)
  have hqq₃ := mul_le_mul_of_nonneg_left hqq₂ (by positivity : 0 ≤ h*b*8*b^4)
  have hc := moment_coefficient_small (b*R) (mul_nonneg hb hR0) hbR
  have hc' := mul_le_mul_of_nonneg_left hc (mul_nonneg hp (sq_nonneg (norm2 f)))
  have he' : h*b*norm2 (J h 1 f)^2 ≤
      10*norm2 (P h (-1) b (J h (-1) f))^2+(1/4:ℝ)*h*b*norm2 f^2 := by
    nlinarith only [he, hq₃, hqq₃, hc']
  have hs := norm2_P_shift h b R hh hb hR0 (by linarith) (by linarith) f hf
  have hs₂ := pow_le_pow_left₀ (norm2_nonneg (P h (-1) b (J h (-1) f))) hs 2
  have hs' : norm2 (P h (-1) b (J h (-1) f))^2 ≤
      2*norm2 (J h (-1) (P h (-1) b f))^2+200*h^2*b^2*norm2 f^2 := by
    nlinarith only [hs₂, sq_nonneg (norm2 (J h (-1) (P h (-1) b f))-10*h*b*norm2 f)]
  have hh' := mul_le_mul_of_nonneg_left hhb
    (by positivity : 0 ≤ 2000*h*b*norm2 f^2)
  have hN := pow_le_pow_left₀ hn (norm2_J_one_ge h f) 2
  have hN' := mul_le_mul_of_nonneg_left hN hp
  nlinarith only [he', hs', hh', hN']

lemma convexified_supported (h ε R : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hε : 0 < ε) (hR : 1 ≤ R) (hsmall : (h/ε)*R ≤ 1/8000)
    (f : S) (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    (h / Real.sqrt ε) * norm2 (J h 1 f) ≤
      7 * norm2 (J h (-1) (P h (-1) (h/ε) f)) := by
  have hb : 0 ≤ h/ε := div_nonneg hh hε.le
  have hb' : h/ε ≤ 1/8000 := by
    nlinarith only [mul_le_mul_of_nonneg_left hR hb, hsmall]
  have hhb : h*(h/ε) ≤ 1/8000 := by
    nlinarith only [mul_le_mul_of_nonneg_right hh1 hb, hb']
  have ht := scalar_supported_shift h (h/ε) R hh hh1 hb hR (by linarith) hhb f hf
  have hs := Real.sq_sqrt hε.le
  have hs0 := Real.sqrt_pos.mpr hε
  have he : (h / Real.sqrt ε)^2 = h*(h/ε) := by
    rw [div_pow, hs]
    ring
  have hn0 := norm2_nonneg (J h 1 f)
  have hn1 := norm2_nonneg (J h (-1) (P h (-1) (h/ε) f))
  have hsN : ((h / Real.sqrt ε) * norm2 (J h 1 f))^2 =
      h*(h/ε)*norm2 (J h 1 f)^2 := by rw [mul_pow, he]
  nlinarith only [ht, hsN, mul_nonneg (div_nonneg hh hs0.le) hn0, hn1]

lemma H1_energy (h : ℝ) (f : S) :
    norm2 (J h 1 f)^2 = mass f + h^2*gradientMass f := by
  rw [norm2_J_sq]
  norm_num only [show (1:ℝ)+1=2 by norm_num]
  rw [J_two, ip_integral]
  change (pair f (f-(h:ℂ)^2 • lap f)).re = _
  rw [pair_sub_right, pair_smul_right]
  have hc : (h:ℂ)^2 = ((h^2:ℝ):ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, lap_energy, mass]
  ring

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

lemma d_mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (v : X)
    (f : S) (x : X) :
    d v (mult a f) x = a x * d v f x + fderiv ℝ a x v * f x := by
  rw [d_apply]
  have he : (mult a f : X → ℂ) = a * (f : X → ℂ) := by
    funext y
    exact mult_apply a ha f y
  rw [he, fderiv_mul (ha.1.differentiable (by simp) x) (f.differentiable x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, d_apply]
  ring

lemma mass_bound_two (f g k : S) (A B : ℝ)
    (hab : ∀ x : X, ‖f x‖^2 ≤ A*‖g x‖^2+B*‖k x‖^2) :
    mass f ≤ A*mass g+B*mass k := by
  have hg := (integrable_normSq g).const_mul A
  have hk := (integrable_normSq k).const_mul B
  rw [mass_integral, mass_integral, mass_integral,
    ← integral_const_mul, ← integral_const_mul, ← integral_add hg hk]
  apply integral_mono (integrable_normSq f) (hg.add hk)
  intro x
  simpa only [Complex.normSq_eq_norm_sq, Pi.add_apply] using hab x

lemma mult_mass (a : X → ℂ) (ha : a.HasTemperateGrowth) (A : ℝ)
    (haA : ∀ x, ‖a x‖ ≤ A) (f : S) :
    mass (mult a f) ≤ A^2*mass f := by
  have ht := norm2_bound (mult a f) f A (fun x => by
    rw [mult_apply a ha, norm_mul]
    exact mul_le_mul_of_nonneg_right (haA x) (norm_nonneg _))
  have ht2 := pow_le_pow_left₀ (norm2_nonneg (mult a f)) ht 2
  simpa only [mul_pow, norm2_sq_mass] using ht2

lemma mult_deriv_mass (h : ℝ) (hh : 0 ≤ h) (a : X → ℂ)
    (ha : a.HasTemperateGrowth) (A D : ℝ)
    (haA : ∀ x, ‖a x‖ ≤ A) (had : ∀ x i, h*‖fderiv ℝ a x (e i)‖ ≤ D)
    (f : S) (i : Fin 3) :
    h^2*mass (d (e i) (mult a f)) ≤
      2*A^2*h^2*mass (d (e i) f)+2*D^2*mass f := by
  have ht := mass_bound_two ((h:ℂ) • d (e i) (mult a f)) (d (e i) f) f
    (2*A^2*h^2) (2*D^2) (fun x => by
      have ht := norm_add_le (a x*d (e i) f x) (fderiv ℝ a x (e i)*f x)
      rw [← d_mult_apply a ha, norm_mul, norm_mul] at ht
      have ht' := mul_le_mul_of_nonneg_left ht hh
      have ha' := mul_le_mul_of_nonneg_right (haA x)
        (mul_nonneg hh (norm_nonneg (d (e i) f x)))
      have hd' := mul_le_mul_of_nonneg_right (had x i) (norm_nonneg (f x))
      have hbound : h*‖d (e i) (mult a f) x‖ ≤
          A*h*‖d (e i) f x‖+D*‖f x‖ := by nlinarith only [ht', ha', hd']
      have hb2 := pow_le_pow_left₀ (mul_nonneg hh (norm_nonneg _)) hbound 2
      simp only [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hh]
      nlinarith only [hb2, sq_nonneg (A*h*‖d (e i) f x‖-D*‖f x‖)])
  rw [mass_ofReal_smul] at ht
  exact ht

lemma mult_H1 (h : ℝ) (hh : 0 ≤ h) (a : X → ℂ)
    (ha : a.HasTemperateGrowth) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (haA : ∀ x, ‖a x‖ ≤ A) (had : ∀ x i, h*‖fderiv ℝ a x (e i)‖ ≤ D)
    (f : S) :
    norm2 (J h 1 (mult a f)) ≤ 3*(A+D)*norm2 (J h 1 f) := by
  have hm := mult_mass a ha A haA f
  have hd0 := mult_deriv_mass h hh a ha A D haA had f 0
  have hd1 := mult_deriv_mass h hh a ha A D haA had f 1
  have hd2 := mult_deriv_mass h hh a ha A D haA had f 2
  have hgrad : h^2*gradientMass (mult a f) ≤
      2*A^2*h^2*gradientMass f+6*D^2*mass f := by
    simp only [gradientMass, Fin.sum_univ_three]
    linarith only [hd0, hd1, hd2]
  have hn := H1_energy h (mult a f)
  have hn' := H1_energy h f
  have hc : A^2+6*D^2 ≤ (3*(A+D))^2 := by nlinarith [mul_nonneg hA hD]
  have hc' : 2*A^2 ≤ (3*(A+D))^2 := by nlinarith [mul_nonneg hA hD]
  have hb₀ := mul_le_mul_of_nonneg_right hc (mass_nonneg f)
  have hb₁ := mul_le_mul_of_nonneg_right hc'
    (mul_nonneg (sq_nonneg h) (gradientMass_nonneg f))
  have hb : norm2 (J h 1 (mult a f))^2 ≤ (3*(A+D)*norm2 (J h 1 f))^2 := by
    nlinarith only [hm, hgrad, hn, hn', hb₀, hb₁]
  exact (sq_le_sq₀ (norm2_nonneg _)
    (mul_nonneg (by positivity) (norm2_nonneg _))).mp hb

lemma temperate_conj (a : X → ℂ) (ha : a.HasTemperateGrowth) :
    (fun x => star (a x)).HasTemperateGrowth :=
  Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth.comp ha

lemma fderiv_conj (a : X → ℂ) (ha : a.HasTemperateGrowth) (x v : X) :
    fderiv ℝ (fun x => star (a x)) x v = star (fderiv ℝ a x v) := by
  exact congrArg (fun L : X →L[ℝ] ℂ => L v)
    (Complex.conjCLE.hasFDerivAt.comp x
      (ha.1.differentiable (by simp) x).hasFDerivAt).fderiv

lemma ip_mult (a : X → ℂ) (ha : a.HasTemperateGrowth) (f g : S) :
    ip (mult a f) g = ip f (mult (fun x => star (a x)) g) := by
  simp only [ip_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [mult_apply a ha, mult_apply _ (temperate_conj a ha)]
  simp only [star_mul]
  ring

lemma ip_shift (h : ℝ) (f g : S) :
    ip f g = ip (J h (-1) f) (J h 1 g) := by
  rw [ip_J, ← J_add_order]
  norm_num

lemma ip_re_shift_bound (h : ℝ) (f g : S) :
    (ip f g).re ≤ norm2 (J h (-1) f)*norm2 (J h 1 g) := by
  rw [ip_shift h]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

lemma mult_Hneg1 (h : ℝ) (hh : 0 ≤ h) (a : X → ℂ)
    (ha : a.HasTemperateGrowth) (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (haA : ∀ x, ‖a x‖ ≤ A) (had : ∀ x i, h*‖fderiv ℝ a x (e i)‖ ≤ D)
    (f : S) :
    norm2 (J h (-1) (mult a f)) ≤ 3*(A+D)*norm2 (J h (-1) f) := by
  let w := mult a f
  let g := J h (-2) w
  have had' : ∀ x i, h*‖fderiv ℝ (fun y => star (a y)) x (e i)‖ ≤ D := by
    intro x i
    rw [fderiv_conj a ha, norm_star]
    exact had x i
  have hm := mult_H1 h hh (fun x => star (a x)) (temperate_conj a ha) A D hA hD
    (fun x => by simpa only [norm_star] using haA x) had' g
  have hj : J h 1 g = J h (-1) w := by
    dsimp only [g]
    rw [← J_add_order]
    norm_num
  rw [hj] at hm
  have hn : norm2 (J h (-1) w)^2 = (ip w g).re := by
    dsimp only [g]
    convert norm2_J_sq h (-1) w using 1; norm_num
  have hpair : ip w g = ip f (mult (fun x => star (a x)) g) := ip_mult a ha f g
  rw [hpair] at hn
  have hi := ip_re_shift_bound h f (mult (fun x => star (a x)) g)
  have hm' := mul_le_mul_of_nonneg_left hm (norm2_nonneg (J h (-1) f))
  have hbound : norm2 (J h (-1) w)^2 ≤
      (3*(A+D)*norm2 (J h (-1) f))*norm2 (J h (-1) w) := by
    nlinarith only [hn, hi, hm']
  have hn0 := norm2_nonneg (J h (-1) w)
  have hc0 : 0 ≤ 3*(A+D)*norm2 (J h (-1) f) :=
    mul_nonneg (by positivity) (norm2_nonneg _)
  change norm2 (J h (-1) w) ≤ _
  nlinarith only [hbound, hn0, hc0]

lemma norm2_sum_le {ι : Type*} (T : Finset ι) (f : ι → S) :
    norm2 (∑ i ∈ T, f i) ≤ ∑ i ∈ T, norm2 (f i) := by
  simpa only [norm2, map_sum] using norm_sum_le T (fun i => L2 (f i))

lemma norm2_mult (a : X → ℂ) (ha : a.HasTemperateGrowth) (A : ℝ)
    (haA : ∀ x, ‖a x‖ ≤ A) (f : S) : norm2 (mult a f) ≤ A*norm2 f := by
  apply norm2_bound
  intro x
  rw [mult_apply a ha, norm_mul]
  exact mul_le_mul_of_nonneg_right (haA x) (norm_nonneg _)

lemma norm2_G_supported (b R : ℝ) (hb : 0 ≤ b) (hR : 0 ≤ R) (hbR : b*R ≤ 1)
    (f : S) (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (G (-1) b f) ≤ 2*norm2 f := by
  have he : G (-1) b f = -f+(b:ℂ) • Q₀ f := by
    simp only [G, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    push_cast
    module
  rw [he]
  have ht := norm2_add_le (-f) ((b:ℂ) • Q₀ f)
  have hn : norm2 (-f) = norm2 f := by simp only [norm2, map_neg, norm_neg]
  rw [hn, norm2_real_smul, abs_of_nonneg hb] at ht
  have hq := mul_le_mul_of_nonneg_left (norm2_Q_supported R hR f hf) hb
  have hc := mul_le_mul_of_nonneg_right hbR (norm2_nonneg f)
  nlinarith only [ht, hq, hc]

lemma norm2_conjugatedDeriv (h b R : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hbR : b*R ≤ 1) (f : S)
    (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) (i : Fin 3) :
    norm2 (conjugatedDeriv h b i f) ≤ 3*h*norm2 (J h 1 f) := by
  have hd := semideriv_bound h 1 hh i f
  norm_num only [sub_self, J_zero] at hd
  have hd' := mul_le_mul_of_nonneg_left hd hh
  have hg := norm2_G_supported b R hb hR hbR f hf
  have hg' := mul_le_mul_of_nonneg_left hg hh
  have hf' := mul_le_mul_of_nonneg_left (norm2_J_one_ge h f) hh
  unfold conjugatedDeriv
  split_ifs with hi
  · have ht := norm2_sub_le (((h^2:ℝ):ℂ) • d (e i) f) ((h:ℂ) • G (-1) b f)
    rw [norm2_real_smul, norm2_real_smul, abs_of_nonneg (sq_nonneg h), abs_of_nonneg hh] at ht
    nlinarith only [ht, hd', hg', hf']
  · simp only [sub_zero, norm2_real_smul, abs_of_nonneg (sq_nonneg h)]
    have hn := mul_nonneg hh (norm2_nonneg (J h 1 f))
    nlinarith only [hd', hn]

lemma norm2_lowerOrder (h b R : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hbR : b*R ≤ 1) (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ i x, ‖a i x‖ ≤ A) (hvV : ∀ x, ‖v x‖ ≤ V)
    (f : S) (hf : ∀ x : X, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (lowerOrder h b a v f) ≤ (9*A+V)*h*norm2 (J h 1 f) := by
  have hd (i : Fin 3) : norm2 (mult (a i) (conjugatedDeriv h b i f)) ≤
      3*A*h*norm2 (J h 1 f) := by
    have ht := norm2_mult (a i) (ha i) A (haA i) (conjugatedDeriv h b i f)
    have hc := mul_le_mul_of_nonneg_left
      (norm2_conjugatedDeriv h b R hh hb hR hbR f hf i) hA
    nlinarith only [ht, hc]
  have hdSum := norm2_sum_le Finset.univ (fun i => mult (a i) (conjugatedDeriv h b i f))
  simp only [Fin.sum_univ_three] at hdSum
  have hv' := norm2_mult v hv V hvV f
  have hv'' := mul_le_mul_of_nonneg_left hv' (sq_nonneg h)
  have hn := norm2_J_one_ge h f
  have hn' := mul_le_mul_of_nonneg_left hn (mul_nonneg hV hh)
  have hsmall := mul_le_mul_of_nonneg_right hh1
    (mul_nonneg (mul_nonneg hh hV) (norm2_nonneg f))
  have ht := norm2_add_le (∑ i : Fin 3, mult (a i) (conjugatedDeriv h b i f))
    (((h^2:ℝ):ℂ) • mult v f)
  rw [norm2_real_smul, abs_of_nonneg (sq_nonneg h)] at ht
  change norm2 (lowerOrder h b a v f) ≤ _ at ht
  simp only [Fin.sum_univ_three] at ht
  nlinarith only [ht, hdSum, hd 0, hd 1, hd 2, hv'', hn', hsmall]

lemma sumNorm_nonneg {n : ℕ} (h s : ℝ) (U : Fin n → S) : 0 ≤ sumNorm h s U :=
  Finset.sum_nonneg (fun _ _ => norm2_nonneg _)

lemma sobNorm_le_sumNorm {n : ℕ} (h s : ℝ) (U : Fin n → S) :
    sobNorm h s U ≤ sumNorm h s U := by
  have hn : 0 ≤ ∑ i, norm2 (J h s (U i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have ht := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => norm2 (J h s (U i))) (fun _ _ => norm2_nonneg _)
  dsimp only [sobNorm, sumNorm]
  have hsum := sumNorm_nonneg h s U
  dsimp only [sumNorm] at hsum
  nlinarith only [hs, ht, hsum, Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2)]

lemma sumNorm_four_le (h s : ℝ) (U : Fin 4 → S) :
    sumNorm h s U ≤ 2*sobNorm h s U := by
  have hn : 0 ≤ ∑ i, norm2 (J h s (U i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have ht := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i => norm2 (J h s (U i)))
  norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at ht
  dsimp only [sobNorm, sumNorm]
  nlinarith only [hs, ht, Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2)]

lemma lowerSystem_bound {n : ℕ} (h b R : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hb : 0 ≤ b) (hR : 0 ≤ R) (hbR : b*R ≤ 1)
    (a : Fin 3 → Fin n → Fin n → X → ℂ) (v : Fin n → Fin n → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ k i j x, ‖a k i j x‖ ≤ A) (hvV : ∀ i j x, ‖v i j x‖ ≤ V)
    (U : Fin n → S) (hU : ∀ i x, U i x ≠ 0 → |x 0| ≤ R) :
    sumNorm h (-1) (lowerSystem h b a v U) ≤
      (n*(9*A+V))*h*sumNorm h 1 U := by
  have hc (i : Fin n) : norm2 (lowerSystem h b a v U i) ≤
      (9*A+V)*h*sumNorm h 1 U := by
    calc
      _ ≤ ∑ j, norm2 (lowerOrder h b (fun k => a k i j) (v i j) (U j)) :=
        norm2_sum_le _ _
      _ ≤ ∑ j, (9*A+V)*h*norm2 (J h 1 (U j)) := Finset.sum_le_sum (fun j _ =>
        norm2_lowerOrder h b R hh hh1 hb hR hbR _ _
          (fun k => ha k i j) (hv i j) A V hA hV (fun k => haA k i j) (hvV i j) (U j) (hU j))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (norm2_J_nonpos h (-1) (by norm_num) (lowerSystem h b a v U i)).trans (hc i))
  simpa only [sumNorm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc] using ht

lemma system_perturbed_l1 {n : ℕ} (h ε R : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hε : 0 < ε) (hR : 1 ≤ R) (hsmall : (h/ε)*R ≤ 1/8000)
    (a : Fin 3 → Fin n → Fin n → X → ℂ) (v : Fin n → Fin n → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ k i j x, ‖a k i j x‖ ≤ A) (hvV : ∀ i j x, ‖v i j x‖ ≤ V)
    (habsorb : 14*(n*(9*A+V))*Real.sqrt ε ≤ 1)
    (U : Fin n → S) (hU : ∀ i x, U i x ≠ 0 → |x 0| ≤ R) :
    sumNorm h 1 U ≤ (14*Real.sqrt ε/h) *
      sumNorm h (-1) (fun i => P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i) := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    convexified_supported h ε R hh.le hh1 hε hR hsmall (U i) (hU i))
  simp only [← Finset.mul_sum] at ht
  change (h/Real.sqrt ε)*sumNorm h 1 U ≤
    7*sumNorm h (-1) (fun i => P h (-1) (h/ε) (U i)) at ht
  have hp := lowerSystem_bound h (h/ε) R hh.le hh1 (div_nonneg hh.le hε.le)
    (by linarith) (by linarith) a v ha hv A V hA hV haA hvV U hU
  have hn0 (i : Fin n) : norm2 (J h (-1) (P h (-1) (h/ε) (U i))) ≤
      norm2 (J h (-1) (P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i))+
      norm2 (J h (-1) (lowerSystem h (h/ε) a v U i)) := by
    have he : P h (-1) (h/ε) (U i) =
      (P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i)-lowerSystem h (h/ε) a v U i := by abel
    have hn := norm2_sub_le
      (J h (-1) (P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i))
      (J h (-1) (lowerSystem h (h/ε) a v U i))
    rwa [← J_sub, ← he] at hn
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hn0 i)
  rw [Finset.sum_add_distrib] at hn
  change sumNorm h (-1) (fun i => P h (-1) (h/ε) (U i)) ≤
    sumNorm h (-1) (fun i => P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i) +
    sumNorm h (-1) (lowerSystem h (h/ε) a v U) at hn
  have hs0 := Real.sqrt_pos.mpr hε
  have hts := mul_le_mul_of_nonneg_left ht hs0.le
  have hs : Real.sqrt ε * (h / Real.sqrt ε) = h := by field_simp
  rw [← mul_assoc, hs] at hts
  have hb := mul_le_mul_of_nonneg_right habsorb
    (mul_nonneg hh.le (sumNorm_nonneg h 1 U))
  have hn' := mul_le_mul_of_nonneg_left hn hs0.le
  have hp' := mul_le_mul_of_nonneg_left hp hs0.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hh).mpr
  nlinarith only [hts, hb, hn', hp']

lemma system_four_perturbed (h ε R : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hε : 0 < ε) (hR : 1 ≤ R) (hsmall : (h/ε)*R ≤ 1/8000)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ k i j x, ‖a k i j x‖ ≤ A) (hvV : ∀ i j x, ‖v i j x‖ ≤ V)
    (habsorb : 56*(9*A+V)*Real.sqrt ε ≤ 1)
    (U : Fin 4 → S) (hU : ∀ i x, U i x ≠ 0 → |x 0| ≤ R) :
    sobNorm h 1 U ≤ (28*Real.sqrt ε/h) *
      sobNorm h (-1) (fun i => P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i) := by
  have ht := system_perturbed_l1 h ε R hh hh1 hε hR hsmall a v ha hv A V hA hV haA hvV
    (by norm_num; nlinarith only [habsorb]) U hU
  have hl := sobNorm_le_sumNorm h 1 U
  have hr := sumNorm_four_le h (-1)
    (fun i => P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i)
  have hr' := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 14*Real.sqrt ε/h from
      div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg ε)) hh.le)
  calc
    _ ≤ (14*Real.sqrt ε/h)*(2*sobNorm h (-1)
        (fun i => P h (-1) (h/ε) (U i)+lowerSystem h (h/ε) a v U i)) := hl.trans (ht.trans hr')
    _ = _ := by ring

end

section

lemma BallSupported.d {R : ℝ} {f : S} (hf : BallSupported R f) (v : X) :
    BallSupported R (d v f) := by
  have ht : tsupport (f : X → ℂ) ⊆ {x : X | ‖x‖ ≤ R} :=
    closure_minimal (fun x hx => hf x hx) (isClosed_le continuous_norm continuous_const)
  intro x hx
  exact ht ((tsupport_fderiv_apply_subset ℝ v) (subset_closure hx))

lemma BallSupported.Q {R : ℝ} {f : S} (hf : BallSupported R f) :
    BallSupported R (Q f) := by
  intro x hx
  exact hf x (fun h => hx (by simp [ElasticitySchwartzCarleman.Q_apply, h]))

lemma BallSupported.mult {R : ℝ} {f : S} (hf : BallSupported R f)
    (a : X → ℂ) (ha : a.HasTemperateGrowth) : BallSupported R (mult a f) := by
  intro x hx
  exact hf x (fun h => hx (by rw [mult_apply a ha, h, mul_zero]))

lemma BallSupported.coordinate {R : ℝ} {f : S} (hf : BallSupported R f) :
    ∀ x : X, f x ≠ 0 → |x 0| ≤ R := by
  intro x hx
  have hc : |x 0| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
  exact hc.trans (hf x hx)

lemma smooth_expQuad (c : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (expQuad c) :=
  (contDiff_const.mul (qCLM.contDiff.pow 2)).cexp

lemma fderiv_expQuad (c : ℂ) (x v : X) :
    fderiv ℝ (expQuad c) x v = expQuad c x*c*qCLM x*qCLM v := by
  have hd := (((qCLM.hasFDerivAt (x := x)).mul (qCLM.hasFDerivAt (x := x))).const_mul (c/2)).cexp
  have he := congrArg (fun L : X →L[ℝ] ℂ => L v) hd.fderiv
  change fderiv ℝ (fun y => Complex.exp ((c/2)*(qCLM y*qCLM y))) x v = _ at he
  simp only [Pi.mul_apply, add_apply, smul_apply,
    smul_eq_mul] at he
  unfold expQuad
  simp_rw [pow_two]
  rw [he]
  ring

lemma compact_weightCut (R : ℝ) (hR : 1 ≤ R) (c : ℂ) :
    HasCompactSupport (weightCut R hR c) := by
  apply HasCompactSupport.mul_right
  exact (cutoff R hR).hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

lemma smooth_weightCut (R : ℝ) (hR : 1 ≤ R) (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (weightCut R hR c) :=
  (Complex.ofRealCLM.contDiff.comp (cutoff R hR).contDiff).mul (smooth_expQuad c)

lemma temperate_weightCut (R : ℝ) (hR : 1 ≤ R) (c : ℂ) :
    (weightCut R hR c).HasTemperateGrowth :=
  (compact_weightCut R hR c).hasTemperateGrowth (smooth_weightCut R hR c)

lemma W_apply (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (f : S)
    (hf : BallSupported R f) (x : X) : W R hR c f x = expQuad c x*f x := by
  rw [W, mult_apply _ (temperate_weightCut R hR c)]
  by_cases hx : f x = 0
  · simp only [hx, mul_zero]
  · have hc : cutoff R hR x = 1 := (cutoff R hR).one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      change ‖x‖ ≤ R+1
      linarith [hf x hx])
    simp only [weightCut, hc, Complex.ofReal_one, one_mul]

lemma BallSupported.W {R : ℝ} {f : S} (hf : BallSupported R f) (hR : 1 ≤ R) (c : ℂ) :
    BallSupported R (W R hR c f) := hf.mult _ (temperate_weightCut R hR c)

lemma d_W (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (f : S) (hf : BallSupported R f) (v : X) :
    d v (W R hR c f) = W R hR c (d v f+(c*qCLM v) • Q f) := by
  ext x
  rw [W_apply R hR c _ ((hf.d v).add (hf.Q.smul _)), d_apply]
  have he : (W R hR c f : X → ℂ) = fun x => expQuad c x*f x :=
    funext (W_apply R hR c f hf)
  rw [he]
  change (fderiv ℝ (expQuad c * (f : X → ℂ)) x) v = _
  rw [fderiv_mul ((smooth_expQuad c).differentiable (by simp) x) (f.differentiable x)]
  simp only [add_apply, smul_apply, smul_eq_mul, ElasticitySchwartzCarleman.Q_apply, d_apply, fderiv_expQuad,
    qCLM_apply]
  ring

lemma lap_W (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (f : S) (hf : BallSupported R f) :
    lap (W R hR c f) = W R hR c (lap f+(2*c) • Q (d (e 0) f)+c • f+c^2 • Q (Q f)) := by
  have hv (v : X) :
      d v (d v (W R hR c f)) = W R hR c
        (d v (d v f)+(2*c*qCLM v) • Q (d v f)+
          (c*(qCLM v)^2) • f+(c^2*(qCLM v)^2) • Q (Q f)) := by
    rw [d_W R hR c f hf v, d_W R hR c _ ((hf.d v).add (hf.Q.smul _)) v]
    simp only [map_add, map_smul, d_Q, smul_add, smul_smul]
    module
  simp only [lap_apply, hv, map_add, map_smul, qCLM_e]
  norm_num [show (2 : Fin 3) ≠ 0 by decide]
  module

lemma W_inverse (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (f : S) (hf : BallSupported R f) :
    W R hR (-c) (W R hR c f) = f := by
  ext x
  rw [W_apply R hR (-c) _ (hf.W hR c), W_apply R hR c f hf]
  simp only [expQuad, ← mul_assoc, ← Complex.exp_add]
  have he : (-c/2)*(qCLM x)^2+(c/2)*(qCLM x)^2 = 0 := by ring
  rw [he, Complex.exp_zero, one_mul]

lemma Q_W (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (f : S) :
    Q (W R hR c f) = W R hR c (Q f) := by
  ext x
  simp only [ElasticitySchwartzCarleman.Q_apply, W,
    mult_apply _ (temperate_weightCut R hR c)]
  ring

lemma mult_W (R : ℝ) (hR : 1 ≤ R) (c : ℂ) (f : S)
    (a : X → ℂ) (ha : a.HasTemperateGrowth) :
    mult a (W R hR c f) = W R hR c (mult a f) := by
  ext x
  simp only [W, mult_apply _ ha, mult_apply _ (temperate_weightCut R hR c)]
  ring

lemma P_W (R : ℝ) (hR : 1 ≤ R) (c h : ℝ) (f : S) (hf : BallSupported R f) :
    P h (-1) (h*c) (W R hR c f) = W R hR c (P h (-1) 0 f) := by
  rw [P_expanded, P_expanded, lap_W R hR c f hf, d_W R hR c f hf]
  simp only [qCLM_e, Q_W, map_add, map_sub, map_smul]
  push_cast
  module

lemma conjugatedDeriv_W (R : ℝ) (hR : 1 ≤ R) (c h : ℝ) (f : S)
    (hf : BallSupported R f) (i : Fin 3) :
    conjugatedDeriv h (h*c) i (W R hR c f) = W R hR c (conjugatedDeriv h 0 i f) := by
  unfold conjugatedDeriv
  rw [d_W R hR c f hf]
  simp only [qCLM_e, G, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Q_W, map_smul, map_add, map_sub]
  split_ifs <;> simp only [map_add, map_smul, map_zero] <;> push_cast <;> module

lemma lowerOrder_W (R : ℝ) (hR : 1 ≤ R) (c h : ℝ) (f : S)
    (hf : BallSupported R f) (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth) :
    lowerOrder h (h*c) a v (W R hR c f) = W R hR c (lowerOrder h 0 a v f) := by
  simp only [lowerOrder, conjugatedDeriv_W R hR c h f hf,
    mult_W R hR c _ _ hv, mult_W R hR c _ _ (ha _), map_add, map_smul, map_sum]

lemma compact_mult_bounds (a : X → ℂ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hc : HasCompactSupport a) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 ≤ h → h ≤ 1 → ∀ f : S,
      norm2 (J h 1 (mult a f)) ≤ C*norm2 (J h 1 f) ∧
      norm2 (J h (-1) (mult a f)) ≤ C*norm2 (J h (-1) f) := by
  obtain ⟨x₀, hx₀⟩ := ha.continuous.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  obtain ⟨x₁, hx₁⟩ := (ha.continuous_fderiv (by simp)).norm.exists_forall_ge_of_hasCompactSupport
    (hc.fderiv ℝ).norm
  let M := 1+‖a x₀‖+‖fderiv ℝ a x₁‖
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨6*M, by positivity, fun h hh hh1 f => ?_⟩
  have hb : ∀ x, ‖a x‖ ≤ M := fun x => by
    dsimp only [M]; linarith [hx₀ x, norm_nonneg (fderiv ℝ a x₁)]
  have hd : ∀ x i, h*‖fderiv ℝ a x (e i)‖ ≤ M := by
    intro x i
    have he : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
    have hop := (fderiv ℝ a x).le_opNorm (e i)
    rw [he, mul_one] at hop
    calc
      _ ≤ ‖fderiv ℝ a x (e i)‖ := by nlinarith only [hh1, norm_nonneg (fderiv ℝ a x (e i))]
      _ ≤ ‖fderiv ℝ a x‖ := hop
      _ ≤ M := by dsimp only [M]; linarith [hx₁ x, norm_nonneg (a x₀)]
  constructor
  · convert mult_H1 h hh a (hc.hasTemperateGrowth ha) M M hM.le hM.le hb hd f using 1; ring
  · convert mult_Hneg1 h hh a (hc.hasTemperateGrowth ha) M M hM.le hM.le hb hd f using 1; ring

lemma sobNorm_map_bound {n : ℕ} (h s C : ℝ) (hC : 0 ≤ C) (T : S → S)
    (hT : ∀ f, norm2 (J h s (T f)) ≤ C*norm2 (J h s f)) (U : Fin n → S) :
    sobNorm h s (fun i => T (U i)) ≤ C*sobNorm h s U := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (sq_le_sq₀ (norm2_nonneg _) (mul_nonneg hC (norm2_nonneg _))).mpr (hT (U i)))
  simp_rw [mul_pow] at ht
  rw [← Finset.mul_sum] at ht
  have h₁ := Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg (norm2 (J h s (T (U i))))))
  have h₂ := Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg (norm2 (J h s (U i)))))
  dsimp only [sobNorm]
  nlinarith only [ht, h₁, h₂, Real.sqrt_nonneg (∑ i, norm2 (J h s (T (U i)))^2),
    mul_nonneg hC (Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2))]

lemma lowerSystem_W {n : ℕ} (R : ℝ) (hR : 1 ≤ R) (c h : ℝ)
    (U : Fin n → S) (hU : ∀ i, BallSupported R (U i))
    (a : Fin 3 → Fin n → Fin n → X → ℂ) (v : Fin n → Fin n → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth) (i : Fin n) :
    lowerSystem h (h*c) a v (fun i => W R hR c (U i)) i =
      W R hR c (lowerSystem h 0 a v U i) := by
  simp only [lowerSystem, lowerOrder_W R hR c h _ (hU _) _ _ (fun k => ha k i _) (hv i _), map_sum]

/-- Removal of the fixed quadratic convexification by actual smooth
Schwartz multipliers; the constant is independent of the small parameter h. -/
lemma system_four_real_fixed (ε R : ℝ) (hε : 0 < ε) (hR : 1 ≤ R)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ k i j x, ‖a k i j x‖ ≤ A) (hvV : ∀ i j x, ‖v i j x‖ ≤ V)
    (habsorb : 56*(9*A+V)*Real.sqrt ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → (h/ε)*R ≤ 1/8000 →
    ∀ U : Fin 4 → S, (∀ i, BallSupported R (U i)) →
    sobNorm h 1 U ≤ (C/h)*sobNorm h (-1)
      (fun i => P h (-1) 0 (U i)+lowerSystem h 0 a v U i) := by
  obtain ⟨Cp, hCp, hp⟩ := compact_mult_bounds (weightCut R hR ((1/ε : ℝ) : ℂ))
    (smooth_weightCut R hR _) (compact_weightCut R hR _)
  obtain ⟨Cm, hCm, hm⟩ := compact_mult_bounds (weightCut R hR (-((1/ε : ℝ) : ℂ)))
    (smooth_weightCut R hR _) (compact_weightCut R hR _)
  refine ⟨Cm*(28*Real.sqrt ε)*Cp, by positivity, fun h hh hh1 hsmall U hU => ?_⟩
  let Up : Fin 4 → S := fun i => W R hR ((1/ε : ℝ) : ℂ) (U i)
  let F : Fin 4 → S := fun i => P h (-1) 0 (U i)+lowerSystem h 0 a v U i
  have hinv : (fun i => W R hR (-((1/ε : ℝ) : ℂ)) (Up i)) = U :=
    funext (fun i => W_inverse R hR _ (U i) (hU i))
  have hl := sobNorm_map_bound h 1 Cm hCm.le (W R hR (-((1/ε : ℝ) : ℂ)))
    (fun f => (hm h hh.le hh1 f).1) Up
  rw [hinv] at hl
  have hshift : h/ε = h*(1/ε) := by ring
  have ht := system_four_perturbed h ε R hh hh1 hε hR hsmall a v ha hv A V hA hV haA hvV habsorb
    Up (fun i => ((hU i).W hR _).coordinate)
  have he : (fun i => P h (-1) (h/ε) (Up i)+lowerSystem h (h/ε) a v Up i) =
      fun i => W R hR ((1/ε : ℝ) : ℂ) (F i) := by
    funext i
    dsimp only [Up, F]
    rw [hshift, P_W R hR (1/ε) h (U i) (hU i), lowerSystem_W R hR (1/ε) h U hU a v ha hv i,
      map_add]
  rw [he] at ht
  have hr := sobNorm_map_bound h (-1) Cp hCp.le (W R hR ((1/ε : ℝ) : ℂ))
    (fun f => (hp h hh.le hh1 f).2) F
  calc
    _ ≤ Cm*sobNorm h 1 Up := hl
    _ ≤ Cm*((28*Real.sqrt ε/h)*sobNorm h (-1) (fun i => W R hR ((1/ε : ℝ) : ℂ) (F i))) :=
      mul_le_mul_of_nonneg_left ht hCm.le
    _ ≤ Cm*((28*Real.sqrt ε/h)*(Cp*sobNorm h (-1) F)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (by positivity)) hCm.le
    _ = _ := by dsimp only [F]; ring

lemma system_four_real (R : ℝ) (hR : 1 ≤ R)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ k i j x, ‖a k i j x‖ ≤ A) (hvV : ∀ i j x, ‖v i j x‖ ≤ V) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
    ∀ U : Fin 4 → S, (∀ i, BallSupported R (U i)) →
    sobNorm h 1 U ≤ (C/h)*sobNorm h (-1)
      (fun i => P h (-1) 0 (U i)+lowerSystem h 0 a v U i) := by
  let D := 56*(9*A+V)+1
  have hD : 0 < D := by dsimp only [D]; positivity
  let ε := (1/D)^2
  have hε : 0 < ε := sq_pos_of_pos (by positivity)
  have hs : Real.sqrt ε = 1/D := by
    dsimp only [ε]; rw [Real.sqrt_sq (by positivity)]
  have habsorb : 56*(9*A+V)*Real.sqrt ε ≤ 1 := by
    rw [hs, mul_one_div, div_le_iff₀ hD]
    dsimp only [D]; linarith
  obtain ⟨C, hC, hc⟩ := system_four_real_fixed ε R hε hR a v ha hv A V hA hV haA hvV habsorb
  have hR0 : 0 < R := by linarith
  refine ⟨C, min 1 (ε/(8000*R)), hC, by positivity, fun h hh hh₀ U hU => ?_⟩
  have hh1 := hh₀.trans (min_le_left 1 (ε/(8000*R)))
  have hsm := hh₀.trans (min_le_right 1 (ε/(8000*R)))
  have hsmall : (h/ε)*R ≤ 1/8000 := by
    calc
      _ = h*(R/ε) := by ring
      _ ≤ (ε/(8000*R))*(R/ε) := mul_le_mul_of_nonneg_right hsm (by positivity)
      _ = 1/8000 := by field_simp
  exact hc h hh hh1 hsmall U hU

end

lemma norm_osc (β : X) (h : ℝ) (x : X) : ‖osc β h x‖ = 1 := by
  simp [osc, Complex.norm_exp]

lemma smooth_osc (β : X) (h : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (osc β h) := by
  exact ((Complex.ofRealCLM.contDiff.comp ((innerSL ℝ β).contDiff.div_const h)).mul
    contDiff_const).cexp

lemma fderiv_osc (β : X) (h : ℝ) (x v : X) :
    fderiv ℝ (osc β h) x v = osc β h x * (((inner ℝ β v / h : ℝ) : ℂ)*Complex.I) := by
  let L : X →L[ℝ] ℂ := Complex.ofRealCLM.comp ((h⁻¹ : ℝ) • innerSL ℝ β)
  have hL : ∀ x, L x = ((inner ℝ β x/h : ℝ) : ℂ) := by
    intro x
    simp only [L, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
      Complex.ofRealCLM_apply ]
    congr 1
    change h⁻¹ * inner ℝ β x = inner ℝ β x/h
    ring
  have hd := ((L.hasFDerivAt (x := x)).mul_const Complex.I).cexp
  have he := congrArg (fun K : X →L[ℝ] ℂ => K v) hd.fderiv
  simp only [smul_apply, smul_eq_mul, hL] at he
  change fderiv ℝ (osc β h) x v = osc β h x*(Complex.I * (((inner ℝ β v/h : ℝ) : ℂ))) at he
  rw [he]
  ring

lemma semideriv_osc (β : X) (h : ℝ) (hh : 0 < h) (x v : X) :
    h*‖fderiv ℝ (osc β h) x v‖ ≤ ‖β‖*‖v‖ := by
  rw [fderiv_osc, norm_mul, norm_osc, one_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hh]
  rw [mul_div_cancel₀ _ hh.ne']
  exact abs_real_inner_le_norm β v

lemma compact_oscCut (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) :
    HasCompactSupport (oscCut R hR β h) :=
  ((cutoff R hR).hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right

lemma smooth_oscCut (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (oscCut R hR β h) :=
  (Complex.ofRealCLM.contDiff.comp (cutoff R hR).contDiff).mul (smooth_osc β h)

lemma temperate_oscCut (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) :
    (oscCut R hR β h).HasTemperateGrowth :=
  (compact_oscCut R hR β h).hasTemperateGrowth (smooth_oscCut R hR β h)

lemma O_apply (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S)
    (hf : BallSupported R f) (x : X) : O R hR β h f x = osc β h x*f x := by
  rw [O, mult_apply _ (temperate_oscCut R hR β h)]
  by_cases hx : f x = 0
  · simp only [hx, mul_zero]
  · have hc : cutoff R hR x = 1 := (cutoff R hR).one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_zero_right]
      change ‖x‖ ≤ R+1
      linarith [hf x hx])
    simp only [oscCut, hc, Complex.ofReal_one, one_mul]

lemma BallSupported.O {R : ℝ} {f : S} (hf : BallSupported R f) (hR : 1 ≤ R) (β : X) (h : ℝ) :
    BallSupported R (O R hR β h f) := hf.mult _ (temperate_oscCut R hR β h)

lemma O_inverse (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S) (hf : BallSupported R f) :
    O R hR (-β) h (O R hR β h f) = f := by
  ext x
  rw [O_apply R hR (-β) h _ (hf.O hR β h), O_apply R hR β h f hf]
  simp only [osc, ← mul_assoc, ← Complex.exp_add, inner_neg_left, neg_div, Complex.ofReal_neg]
  rw [neg_mul, neg_add_cancel, Complex.exp_zero, one_mul]

lemma osc_multiplier_bounds (R : ℝ) (hR : 1 ≤ R) (β : X) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : S,
      norm2 (J h 1 (O R hR β h f)) ≤ C*norm2 (J h 1 f) ∧
      norm2 (J h (-1) (O R hR β h f)) ≤ C*norm2 (J h (-1) f) := by
  let ac : X → ℂ := fun x => (cutoff R hR x : ℂ)
  have hac : ContDiff ℝ (⊤ : ℕ∞) ac :=
    Complex.ofRealCLM.contDiff.comp (cutoff R hR).contDiff
  have hacc : HasCompactSupport ac :=
    (cutoff R hR).hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  obtain ⟨x₀, hx₀⟩ := (hac.continuous_fderiv (by simp)).norm.exists_forall_ge_of_hasCompactSupport
    (hacc.fderiv ℝ).norm
  let D := ‖fderiv ℝ ac x₀‖
  have hD : 0 ≤ D := norm_nonneg _
  have hdc (x : X) (i : Fin 3) : ‖fderiv ℝ ac x (e i)‖ ≤ D := by
    have he : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
    have hc := (fderiv ℝ ac x).le_opNorm (e i)
    rw [he, mul_one] at hc
    exact hc.trans (hx₀ x)
  have hacb (x : X) : ‖ac x‖ ≤ 1 := by
    simp only [ac, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoff R hR).nonneg]
    exact (cutoff R hR).le_one
  refine ⟨3*(1+(D+‖β‖)), by positivity, fun h hh hh1 f => ?_⟩
  have hb (x : X) : ‖oscCut R hR β h x‖ ≤ 1 := by
    simp only [oscCut, norm_mul, norm_osc, mul_one]
    exact hacb x
  have hd (x : X) (i : Fin 3) : h*‖fderiv ℝ (oscCut R hR β h) x (e i)‖ ≤ D+‖β‖ := by
    have he : ‖e i‖ = 1 := by simp [e, PiLp.norm_single]
    have hosc := semideriv_osc β h hh x (e i)
    rw [he, mul_one] at hosc
    have heq : oscCut R hR β h = ac * osc β h := rfl
    rw [heq, fderiv_mul (hac.differentiable (by simp) x) ((smooth_osc β h).differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have ht := norm_add_le (ac x*fderiv ℝ (osc β h) x (e i))
      (osc β h x*fderiv ℝ ac x (e i))
    rw [norm_mul, norm_mul, norm_osc, one_mul] at ht
    have ht' := mul_le_mul_of_nonneg_left ht hh.le
    have hab := mul_le_mul_of_nonneg_right (hacb x) (norm_nonneg (fderiv ℝ (osc β h) x (e i)))
    have hab' := mul_le_mul_of_nonneg_left hab hh.le
    have hdc' := mul_le_mul_of_nonneg_left (hdc x i) hh.le
    have hD' := mul_le_mul_of_nonneg_right hh1 hD
    nlinarith only [ht', hab', hdc', hD', hosc]
  exact ⟨mult_H1 h hh.le _ (temperate_oscCut R hR β h) 1 (D+‖β‖)
    (by norm_num) (by positivity) hb hd f,
    mult_Hneg1 h hh.le _ (temperate_oscCut R hR β h) 1 (D+‖β‖)
    (by norm_num) (by positivity) hb hd f⟩

lemma BallSupported.sub {R : ℝ} {f g : S} (hf : BallSupported R f)
    (hg : BallSupported R g) : BallSupported R (f-g) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hf.add (hg.smul (-1))

lemma BallSupported.sum {ι : Type*} (T : Finset ι) {R : ℝ} (f : ι → S)
    (hf : ∀ i ∈ T, BallSupported R (f i)) : BallSupported R (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using BallSupported.zero R
  | @insert i T hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma BallSupported.lap {R : ℝ} {f : S} (hf : BallSupported R f) :
    BallSupported R (lap f) := by
  rw [lap_apply]
  exact ((hf.d (e 0)).d (e 0) |>.add ((hf.d (e 1)).d (e 1))).add ((hf.d (e 2)).d (e 2))

lemma BallSupported.P_zero {R : ℝ} {f : S} (hf : BallSupported R f) (h : ℝ) :
    BallSupported R (P h (-1) 0 f) := by
  have he : P h (-1) 0 f = ((-h^2 : ℝ) : ℂ) • ElasticitySchwartzCarleman.lap f - f - ((2*h : ℝ) : ℂ) • ElasticitySchwartzCarleman.d (e 0) f := by
    rw [P_expanded]; simp
  rw [he]
  exact ((hf.lap.smul _).sub hf).sub ((hf.d _).smul _)

lemma BallSupported.conjugatedDeriv_zero {R : ℝ} {f : S} (hf : BallSupported R f)
    (h : ℝ) (i : Fin 3) : BallSupported R (conjugatedDeriv h 0 i f) := by
  unfold conjugatedDeriv
  simp only [G, LinearMap.smul_apply, LinearMap.id_apply,
    Complex.ofReal_zero, zero_smul, add_zero]
  split_ifs
  · exact ((hf.d _).smul _).sub ((hf.smul _).smul _)
  · simpa only [sub_zero] using (hf.d _).smul ((h^2 : ℝ) : ℂ)

lemma BallSupported.lowerOrder_zero {R : ℝ} {f : S} (hf : BallSupported R f)
    (h : ℝ) (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth) :
    BallSupported R (lowerOrder h 0 a v f) :=
  (BallSupported.sum Finset.univ _ (fun i _ => (hf.conjugatedDeriv_zero h i).mult (a i) (ha i))).add
    ((hf.mult v hv).smul _)

lemma BallSupported.lowerSystem_zero {n : ℕ} {R : ℝ} (h : ℝ)
    (U : Fin n → S) (hU : ∀ i, BallSupported R (U i))
    (a : Fin 3 → Fin n → Fin n → X → ℂ) (v : Fin n → Fin n → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth) (i : Fin n) :
    BallSupported R (lowerSystem h 0 a v U i) :=
  BallSupported.sum Finset.univ _ (fun j _ =>
    (hU j).lowerOrder_zero h _ _ (fun k => ha k i j) (hv i j))

lemma system_four_phase (R : ℝ) (hR : 1 ≤ R) (β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (A V : ℝ) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (haA : ∀ k i j x, ‖a k i j x‖ ≤ A) (hvV : ∀ i j x, ‖v i j x‖ ≤ V) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
    ∀ U : Fin 4 → S, (∀ i, BallSupported R (U i)) →
    sobNorm h 1 U ≤ (C/h)*sobNorm h (-1) (phaseSystem R hR β h a v U) := by
  obtain ⟨Cp, hCp, hp⟩ := osc_multiplier_bounds R hR β
  obtain ⟨Cm, hCm, hm⟩ := osc_multiplier_bounds R hR (-β)
  obtain ⟨C, h₀, hC, hh₀, hc⟩ := system_four_real R hR a v ha hv A V hA hV haA hvV
  refine ⟨Cm*C*Cp, min h₀ 1, by positivity, by positivity, fun h hh hhsmall U hU => ?_⟩
  have hh1 := hhsmall.trans (min_le_right h₀ 1)
  have hh0 := hhsmall.trans (min_le_left h₀ 1)
  let Up : Fin 4 → S := fun i => O R hR β h (U i)
  have hUp (i : Fin 4) : BallSupported R (Up i) := (hU i).O hR β h
  let F : Fin 4 → S := fun i => P h (-1) 0 (Up i)+lowerSystem h 0 a v Up i
  have hF (i : Fin 4) : BallSupported R (F i) :=
    ((hUp i).P_zero h).add (BallSupported.lowerSystem_zero h Up hUp a v ha hv i)
  have hinv : (fun i => O R hR (-β) h (Up i)) = U :=
    funext (fun i => O_inverse R hR β h (U i) (hU i))
  have hout : (fun i => O R hR β h (phaseSystem R hR β h a v U i)) = F := by
    funext i
    change O R hR β h (O R hR (-β) h (F i)) = F i
    simpa only [neg_neg] using O_inverse R hR (-β) h (F i) (hF i)
  have hl := sobNorm_map_bound h 1 Cm hCm.le (O R hR (-β) h)
    (fun f => (hm h hh hh1 f).1) Up
  rw [hinv] at hl
  have ht := hc h hh hh0 Up hUp
  have hr := sobNorm_map_bound h (-1) Cp hCp.le (O R hR β h)
    (fun f => (hp h hh hh1 f).2) (phaseSystem R hR β h a v U)
  rw [hout] at hr
  calc
    _ ≤ Cm*sobNorm h 1 Up := hl
    _ ≤ Cm*((C/h)*sobNorm h (-1) F) := mul_le_mul_of_nonneg_left ht hCm.le
    _ ≤ Cm*((C/h)*(Cp*sobNorm h (-1) (phaseSystem R hR β h a v U))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (by positivity)) hCm.le
    _ = _ := by ring

lemma d_O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S)
    (hf : BallSupported R f) (v : X) :
    d v (O R hR β h f) = O R hR β h (d v f+oscRate β h v • f) := by
  ext x
  rw [O_apply R hR β h _ ((hf.d v).add (hf.smul _)), d_apply]
  have he : (O R hR β h f : X → ℂ) = fun x => osc β h x*f x :=
    funext (O_apply R hR β h f hf)
  rw [he]
  change fderiv ℝ (osc β h * (f : X → ℂ)) x v = _
  rw [fderiv_mul ((smooth_osc β h).differentiable (by simp) x) (f.differentiable x)]
  simp only [add_apply, smul_apply, smul_eq_mul, d_apply, fderiv_osc, oscRate]
  ring

lemma lap_O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S)
    (hf : BallSupported R f) :
    lap (O R hR β h f) = O R hR β h
      (lap f + (∑ i : Fin 3, (2*oscRate β h (e i)) • d (e i) f) +
        (∑ i : Fin 3, (oscRate β h (e i))^2) • f) := by
  have he (v : X) : d v (d v (O R hR β h f)) = O R hR β h
      (d v (d v f)+(2*oscRate β h v) • d v f+(oscRate β h v)^2 • f) := by
    rw [d_O R hR β h f hf v, d_O R hR β h _ ((hf.d v).add (hf.smul _)) v]
    simp only [map_add, map_smul]
    module
  simp only [lap_apply, he, Fin.sum_univ_three, map_add, map_smul]
  module

lemma P_O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S) (hf : BallSupported R f) :
    P h (-1) 0 (O R hR β h f) = O R hR β h (Pbeta h β f) := by
  rw [P_expanded, lap_O R hR β h f hf, d_O R hR β h f hf]
  simp only [Pbeta, map_add, map_smul, map_sub]
  push_cast
  module

lemma conjugatedDeriv_O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S)
    (hf : BallSupported R f) (i : Fin 3) :
    conjugatedDeriv h 0 i (O R hR β h f) = O R hR β h (betaDeriv h β i f) := by
  simp only [conjugatedDeriv, betaDeriv, d_O R hR β h f hf, G,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
  split_ifs <;> simp only [map_zero, map_smul] <;> push_cast <;> module

lemma mult_O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S)
    (a : X → ℂ) (ha : a.HasTemperateGrowth) :
    mult a (O R hR β h f) = O R hR β h (mult a f) := by
  ext x
  simp only [O, mult_apply _ ha, mult_apply _ (temperate_oscCut R hR β h)]
  ring

lemma lowerOrder_O (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ) (f : S)
    (hf : BallSupported R f) (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth) :
    lowerOrder h 0 a v (O R hR β h f) = O R hR β h (lowerBeta h β a v f) := by
  simp only [lowerOrder, lowerBeta, conjugatedDeriv_O R hR β h f hf,
    mult_O R hR β h _ _ hv, mult_O R hR β h _ _ (ha _), map_add, map_smul, map_sum]

lemma BallSupported.Pbeta {R : ℝ} {f : S} (hf : BallSupported R f) (h : ℝ) (β : X) :
    BallSupported R (Pbeta h β f) := by
  unfold ElasticityNegativeOrder.Pbeta
  apply BallSupported.sub
  · apply BallSupported.sub
    · apply BallSupported.smul
      apply BallSupported.add
      · exact hf.lap.add (BallSupported.sum Finset.univ _ (fun i _ => (hf.d _).smul _))
      · exact hf.smul _
    · exact hf
  · exact ((hf.d _).add (hf.smul _)).smul _

lemma BallSupported.betaDeriv {R : ℝ} {f : S} (hf : BallSupported R f)
    (h : ℝ) (β : X) (i : Fin 3) : BallSupported R (betaDeriv h β i f) := by
  unfold ElasticityNegativeOrder.betaDeriv
  split_ifs
  · exact (((hf.d _).add (hf.smul _)).smul _).add (hf.smul _)
  · simpa only [add_zero] using ((hf.d _).add (hf.smul _)).smul ((h^2 : ℝ) : ℂ)

lemma BallSupported.lowerBeta {R : ℝ} {f : S} (hf : BallSupported R f)
    (h : ℝ) (β : X) (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth) :
    BallSupported R (lowerBeta h β a v f) :=
  (BallSupported.sum Finset.univ _ (fun i _ => (hf.betaDeriv h β i).mult (a i) (ha i))).add
    ((hf.mult v hv).smul _)

lemma phaseSystem_eq_betaSystem (R : ℝ) (hR : 1 ≤ R) (β : X) (h : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (U : Fin 4 → S) (hU : ∀ i, BallSupported R (U i)) :
    phaseSystem R hR β h a v U = betaSystem h β a v U := by
  funext i
  simp only [phaseSystem, P_O R hR β h (U i) (hU i), lowerSystem,
    lowerOrder_O R hR β h _ (hU _) _ _ (fun k => ha k i _) (hv i _), ← map_sum, ← map_add]
  exact O_inverse R hR β h _ (((hU i).Pbeta h β).add
    (BallSupported.sum Finset.univ _ (fun j _ => (hU j).lowerBeta h β _ _ (fun k => ha k i j) (hv i j))))

lemma fourier_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) : 𝓕 (rot A f) = rot A (𝓕 f) := by
  ext x
  exact Real.fourier_comp_linearIsometry A f x

lemma fourierInv_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) : 𝓕⁻ (rot A f) = rot A (𝓕⁻ f) := by
  ext x
  change (𝓕⁻ (rot A f)) x = (𝓕⁻ f) (A x)
  simp only [SchwartzMap.fourierInv_coe]
  exact Real.fourierInv_comp_linearIsometry A f x

lemma M_rot (A : X ≃ₗᵢ[ℝ] X) (h s : ℝ) (f : S) :
    M h s (rot A f) = rot A (M h s f) := by
  ext x
  simp only [M_apply, rot_apply, weight, ← map_smul A, A.norm_map]

lemma J_rot (A : X ≃ₗᵢ[ℝ] X) (h s : ℝ) (f : S) :
    J h s (rot A f) = rot A (J h s f) := by
  simp only [J, fourier_rot, M_rot, fourierInv_rot]

lemma mass_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) : mass (rot A f) = mass f := by
  change (∫ x : X, star (f (A x))*f (A x)).re = (∫ x : X, star (f x)*f x).re
  exact congrArg Complex.re (A.measurePreserving.integral_comp
    A.toHomeomorph.measurableEmbedding (fun x : X => star (f x)*f x))

lemma norm2_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) : norm2 (rot A f) = norm2 f := by
  have he : norm2 (rot A f)^2 = norm2 f^2 := by rw [norm2_sq_mass, mass_rot, norm2_sq_mass]
  nlinarith [norm2_nonneg (rot A f), norm2_nonneg f]

lemma sobNorm_rot {n : ℕ} (A : X ≃ₗᵢ[ℝ] X) (h s : ℝ) (U : Fin n → S) :
    sobNorm h s (fun i => rot A (U i)) = sobNorm h s U := by
  simp only [sobNorm, J_rot, norm2_rot]

lemma BallSupported.rot {R : ℝ} {f : S} (hf : BallSupported R f) (A : X ≃ₗᵢ[ℝ] X) :
    BallSupported R (rot A f) := by
  intro x hx
  have ht := hf (A x) hx
  rwa [A.norm_map] at ht

lemma d_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) (v : X) :
    d v (rot A f) = rot A (d (A v) f) :=
  SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℂ v A.toContinuousLinearEquiv f

lemma lap_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) : lap (rot A f) = rot A (lap f) := by
  have ht := J_rot A 1 2 f
  simp only [J_two, Complex.ofReal_one, one_pow, one_smul, map_sub] at ht
  exact (sub_right_inj.mp ht)

lemma d_sum_basis (v : X) (f : S) : d v f = ∑ i : Fin 3, (v i : ℂ) • d (e i) f := by
  ext x
  simp only [d_apply, sum_apply, smul_apply, smul_eq_mul]
  have hv : v = ∑ i : Fin 3, (v i) • e i := by
    ext j
    simp only [e, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul]
    fin_cases j <;> simp
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Complex.real_smul]

lemma exists_rotation (α : X) (hα : ‖α‖ = 1) : ∃ A : X ≃ₗᵢ[ℝ] X, A (e 0) = α := by
  refine ⟨(ℝ ∙ (e 0-α))ᗮ.reflection, ?_⟩
  exact Submodule.reflection_sub (by simpa only [e, PiLp.norm_single, norm_one] using hα.symm)

lemma Pbeta_eq_Pdir (h : ℝ) (hh : h ≠ 0) (β : X) (f : S) :
    Pbeta h β f = Pdir h (e 0) β f := by
  ext x
  simp only [Pbeta, Pdir, oscRate, e, EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_left, conj_trivial, one_mul,
    d_sum_basis β f, Fin.sum_univ_three, PiLp.norm_single, norm_one, one_pow,
    EuclideanSpace.real_norm_sq_eq, sub_apply, add_apply, smul_apply, smul_eq_mul]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma betaDeriv_eq_dirDeriv (h : ℝ) (hh : h ≠ 0) (β : X) (i : Fin 3) (f : S) :
    betaDeriv h β i f = dirDeriv h (e 0) β i f := by
  ext x
  simp only [betaDeriv, dirDeriv, oscRate, e, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, PiLp.single_apply, add_apply, smul_apply, smul_eq_mul]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  split_ifs <;> simp only [smul_apply, smul_eq_mul, zero_apply] <;>
    push_cast <;> field_simp [hc] <;> ring

lemma Pdir_rot (A : X ≃ₗᵢ[ℝ] X) (h : ℝ) (α β : X) (f : S) :
    Pdir h α β (rot A f) = rot A (Pdir h (A α) (A β) f) := by
  simp only [Pdir, lap_rot, d_rot, A.norm_map, A.inner_map_map, map_sub, map_smul]

lemma d_basis_rot (A : X ≃ₗᵢ[ℝ] X) (f : S) (i : Fin 3) :
    rot A (d (e i) f) = ∑ k : Fin 3, ((A (e k) i : ℝ) : ℂ) • d (e k) (rot A f) := by
  have he : A.symm (e i) = WithLp.toLp 2 (fun k : Fin 3 => A (e k) i) := by
    ext k
    have hi := A.inner_map_map (A.symm (e i)) (e k)
    simp only [A.apply_symm_apply, e, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul] at hi
    exact hi.symm
  have hd := d_rot A f (A.symm (e i))
  rw [A.apply_symm_apply] at hd
  rw [← hd, d_sum_basis, he]

lemma basis_expansion (v : X) : v = ∑ i : Fin 3, (v i) • e i := by
  ext j
  simp only [e, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  fin_cases j <;> simp

lemma map_coord (A : X ≃ₗᵢ[ℝ] X) (v : X) (i : Fin 3) :
    A v i = ∑ k : Fin 3, A (e k) i * v k := by
  conv_lhs => rw [basis_expansion v]
  simp only [Fin.sum_univ_three, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

lemma dirDeriv_basis_rot (A : X ≃ₗᵢ[ℝ] X) (h : ℝ) (α β : X) (f : S) (i : Fin 3) :
    rot A (dirDeriv h (A α) (A β) i f) =
      ∑ k : Fin 3, (A (e k) i : ℂ) • dirDeriv h α β k (rot A f) := by
  simp only [dirDeriv, map_add, map_smul, d_basis_rot, map_coord A α i, map_coord A β i,
    Fin.sum_univ_three]
  push_cast
  module

lemma temperate_comp_rot (A : X ≃ₗᵢ[ℝ] X) (a : X → ℂ) (ha : a.HasTemperateGrowth) :
    (fun x => a (A x)).HasTemperateGrowth :=
  ha.comp A.toContinuousLinearEquiv.toContinuousLinearMap.hasTemperateGrowth

lemma mult_rot (A : X ≃ₗᵢ[ℝ] X) (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) :
    rot A (mult a f) = mult (fun x => a (A x)) (rot A f) := by
  ext x
  simp only [rot_apply, mult_apply _ ha, mult_apply _ (temperate_comp_rot A a ha)]

lemma betaSystem_eq_dirSystem (h : ℝ) (hh : h ≠ 0) (β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (U : Fin 4 → S) : betaSystem h β a v U = dirSystem h (e 0) β a v U := by
  funext i
  simp only [betaSystem, dirSystem, Pbeta_eq_Pdir h hh, lowerBeta, lowerDir,
    betaDeriv_eq_dirDeriv h hh]

lemma temperate_rotCoeff (A : X ≃ₗᵢ[ℝ] X) (a : Fin 3 → X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (k : Fin 3) :
    (rotCoeff A a k).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.sum
  intro i _
  exact (Function.HasTemperateGrowth.const _).mul (temperate_comp_rot A (a i) (ha i))

lemma norm_rotCoord_le (A : X ≃ₗᵢ[ℝ] X) (k i : Fin 3) : ‖(A (e k) i : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real]
  have ht := PiLp.norm_apply_le (A (e k)) i
  rw [A.norm_map] at ht
  simpa only [e, PiLp.norm_single, norm_one] using ht

lemma norm_rotCoeff_le (A : X ≃ₗᵢ[ℝ] X) (a : Fin 3 → X → ℂ)
    (C : ℝ) (_hC : 0 ≤ C) (ha : ∀ i x, ‖a i x‖ ≤ C) (k : Fin 3) (x : X) :
    ‖rotCoeff A a k x‖ ≤ 3*C := by
  calc
    _ ≤ ∑ i : Fin 3, ‖(A (e k) i : ℂ)*a i (A x)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact (mul_le_mul (norm_rotCoord_le A k i) (ha i (A x)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
    _ = _ := by simp

lemma lowerDir_rot (A : X ≃ₗᵢ[ℝ] X) (h : ℝ) (α β : X)
    (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i, (a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth) (f : S) :
    rot A (lowerDir h (A α) (A β) a v f) =
      lowerDir h α β (rotCoeff A a) (fun x => v (A x)) (rot A f) := by
  simp only [lowerDir, map_add, map_sum, map_smul, mult_rot A _ hv,
    mult_rot A _ (ha _), dirDeriv_basis_rot]
  congr 1
  ext x
  simp only [mult_apply _ (temperate_comp_rot A _ (ha _)),
    mult_apply _ (temperate_rotCoeff A a ha _), rotCoeff, smul_apply, smul_eq_mul,
    Fin.sum_univ_three, add_apply]
  ring

lemma dirSystem_rot (A : X ≃ₗᵢ[ℝ] X) (h : ℝ) (α β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth) (U : Fin 4 → S) :
    (fun i => rot A (dirSystem h (A α) (A β) a v U i)) =
      dirSystem h α β (fun k i j => rotCoeff A (fun l => a l i j) k)
        (fun i j x => v i j (A x)) (fun i => rot A (U i)) := by
  funext i
  simp only [dirSystem, map_add, map_sum, ← Pdir_rot,
    lowerDir_rot A h α β _ _ (fun k => ha k i _) (hv i _)]

lemma system_four_unit_direction (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : ‖α‖ = 1)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (M V : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (haM : ∀ k i j x, ‖a k i j x‖ ≤ M) (hvV : ∀ i j x, ‖v i j x‖ ≤ V) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
    ∀ U : Fin 4 → S, (∀ i, BallSupported R (U i)) →
    sobNorm h 1 U ≤ (C/h)*sobNorm h (-1) (dirSystem h α β a v U) := by
  obtain ⟨Q, hQ⟩ := exists_rotation α hα
  let ar : Fin 3 → Fin 4 → Fin 4 → X → ℂ :=
    fun k i j => rotCoeff Q (fun l => a l i j) k
  let vr : Fin 4 → Fin 4 → X → ℂ := fun i j x => v i j (Q x)
  have har (k : Fin 3) (i j : Fin 4) : (ar k i j).HasTemperateGrowth :=
    temperate_rotCoeff Q _ (fun l => ha l i j) k
  have hvr (i j : Fin 4) : (vr i j).HasTemperateGrowth :=
    temperate_comp_rot Q _ (hv i j)
  have harM (k : Fin 3) (i j : Fin 4) (x : X) : ‖ar k i j x‖ ≤ 3*M :=
    norm_rotCoeff_le Q _ M hM (fun l x => haM l i j x) k x
  obtain ⟨C, h₀, hC, hh₀, hc⟩ := system_four_phase R hR (Q.symm β) ar vr har hvr
    (3*M) V (by positivity) hV harM (fun i j x => hvV i j (Q x))
  refine ⟨C, h₀, hC, hh₀, fun h hh hhsmall U hU => ?_⟩
  have ht := hc h hh hhsmall (fun i => rot Q (U i)) (fun i => (hU i).rot Q)
  rw [phaseSystem_eq_betaSystem R hR _ h ar vr har hvr _ (fun i => (hU i).rot Q),
    betaSystem_eq_dirSystem h hh.ne', sobNorm_rot] at ht
  have he := dirSystem_rot Q h (e 0) (Q.symm β) a v ha hv U
  simp only [hQ, Q.apply_symm_apply] at he
  change (fun i => rot Q (dirSystem h α β a v U i)) =
    dirSystem h (e 0) (Q.symm β) ar vr (fun i => rot Q (U i)) at he
  rw [← he, sobNorm_rot] at ht
  exact ht

lemma weight_one_sq (h : ℝ) (x : X) : (weight h 1 x)^2 = 1+‖(2*Real.pi*h) • x‖^2 := by
  rw [pow_two, ← weight_add]
  norm_num [weight]

lemma weight_hscale_one (r h : ℝ) (hr : 0 ≤ r) (x : X) :
    weight (r*h) 1 x ≤ (1+r)*weight h 1 x := by
  have he : (2*Real.pi*(r*h)) • x = r • ((2*Real.pi*h) • x) := by
    rw [smul_smul]
    congr 1
    ring
  have hs := weight_one_sq (r*h) x
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hs
  have hs' := weight_one_sq h x
  apply (sq_le_sq₀ (weight_pos (r*h) 1 x).le (mul_nonneg (by linarith) (weight_pos h 1 x).le)).mp
  rw [mul_pow, hs, hs', mul_pow]
  have hn : 0 ≤ ‖(2*Real.pi*h) • x‖^2 := sq_nonneg _
  nlinarith [mul_nonneg hr hn, sq_nonneg r]

lemma weight_hscale_neg_one (r h : ℝ) (hr : 0 ≤ r) (x : X) :
    weight h (-1) x ≤ (1+r)*weight (r*h) (-1) x := by
  rw [weight_neg, weight_neg]
  have ht := weight_hscale_one r h hr x
  rw [← one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (weight_pos h 1 x) (weight_pos (r*h) 1 x)).2
  simpa only [one_mul] using ht

lemma norm2_J_of_weight_bound (h k s t C : ℝ)
    (hbound : ∀ x : X, weight h s x ≤ C*weight k t x) (f : S) :
    norm2 (J h s f) ≤ C*norm2 (J k t f) := by
  rw [norm2_J, norm2_J]
  apply norm2_bound
  intro x
  simp only [M_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos h s x), abs_of_pos (weight_pos k t x)]
  calc
    _ ≤ (C*weight k t x)*‖𝓕 f x‖ := mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
    _ = _ := by ring

lemma norm2_J_hscale_one (r h : ℝ) (hr : 0 ≤ r) (f : S) :
    norm2 (J (r*h) 1 f) ≤ (1+r)*norm2 (J h 1 f) :=
  norm2_J_of_weight_bound _ _ _ _ _ (weight_hscale_one r h hr) f

lemma norm2_J_hscale_neg_one (r h : ℝ) (hr : 0 ≤ r) (f : S) :
    norm2 (J h (-1) f) ≤ (1+r)*norm2 (J (r*h) (-1) f) :=
  norm2_J_of_weight_bound _ _ _ _ _ (weight_hscale_neg_one r h hr) f

lemma sobNorm_component_bound {n : ℕ} (h k s t C : ℝ) (hC : 0 ≤ C)
    (U V : Fin n → S) (hb : ∀ i, norm2 (J h s (U i)) ≤ C*norm2 (J k t (V i))) :
    sobNorm h s U ≤ C*sobNorm k t V := by
  have hs : ∑ i, (norm2 (J h s (U i)))^2 ≤ C^2 * ∑ i, (norm2 (J k t (V i)))^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hb i, norm2_nonneg (J h s (U i)), norm2_nonneg (J k t (V i))]
  rw [sobNorm, sobNorm]
  have hp : 0 ≤ ∑ i, (norm2 (J h s (U i)))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hq : 0 ≤ ∑ i, (norm2 (J k t (V i)))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
  exact hs

lemma sobNorm_hscale_one {n : ℕ} (r h : ℝ) (hr : 0 ≤ r) (U : Fin n → S) :
    sobNorm (r*h) 1 U ≤ (1+r)*sobNorm h 1 U :=
  sobNorm_component_bound _ _ _ _ _ (by positivity) U U (fun i => norm2_J_hscale_one r h hr (U i))

lemma sobNorm_hscale_neg_one {n : ℕ} (r h : ℝ) (hr : 0 ≤ r) (U : Fin n → S) :
    sobNorm h (-1) U ≤ (1+r)*sobNorm (r*h) (-1) U :=
  sobNorm_component_bound _ _ _ _ _ (by positivity) U U (fun i => norm2_J_hscale_neg_one r h hr (U i))

lemma d_real_smul (r : ℝ) (v : X) (f : S) : d (r • v) f = (r : ℂ) • d v f := by
  ext x
  simp only [d_apply, map_smul, smul_apply, Complex.real_smul, smul_eq_mul]

lemma Pdir_scale (r h : ℝ) (α β : X) (f : S) :
    Pdir (r*h) (r • α) (r • β) f = ((r^2 : ℝ) : ℂ) • Pdir h α β f := by
  simp only [Pdir, d_real_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, real_inner_smul_right]
  push_cast
  module

lemma dirDeriv_scale (r h : ℝ) (α β : X) (i : Fin 3) (f : S) :
    dirDeriv (r*h) (r • α) (r • β) i f = ((r^2 : ℝ) : ℂ) • dirDeriv h α β i f := by
  simp only [dirDeriv, PiLp.smul_apply, smul_eq_mul]
  push_cast
  module

lemma lowerDir_scale (r h : ℝ) (α β : X) (a : Fin 3 → X → ℂ) (v : X → ℂ) (f : S) :
    lowerDir (r*h) (r • α) (r • β) a v f = ((r^2 : ℝ) : ℂ) • lowerDir h α β a v f := by
  simp only [lowerDir, dirDeriv_scale, map_smul, Fin.sum_univ_three]
  push_cast
  module

lemma dirSystem_scale (r h : ℝ) (α β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (U : Fin 4 → S) :
    dirSystem (r*h) (r • α) (r • β) a v U =
      fun i => ((r^2 : ℝ) : ℂ) • dirSystem h α β a v U i := by
  funext i
  simp only [dirSystem, Pdir_scale, lowerDir_scale, Finset.smul_sum, smul_add]

lemma sobNorm_smul {n : ℕ} (h s : ℝ) (c : ℂ) (U : Fin n → S) :
    sobNorm h s (fun i => c • U i) = ‖c‖*sobNorm h s U := by
  simp only [sobNorm, J_smul, norm2_const_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma system_four_direction (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j, (a k i j).HasTemperateGrowth)
    (hv : ∀ i j, (v i j).HasTemperateGrowth)
    (M V : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V)
    (haM : ∀ k i j x, ‖a k i j x‖ ≤ M) (hvV : ∀ i j x, ‖v i j x‖ ≤ V) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
    ∀ U : Fin 4 → S, (∀ i, BallSupported R (U i)) →
    sobNorm h 1 U ≤ (C/h)*sobNorm h (-1) (dirSystem h α β a v U) := by
  let r := ‖α‖
  have hr : 0 < r := norm_pos_iff.mpr hα
  let α' := r⁻¹ • α
  let β' := r⁻¹ • β
  have hα' : ‖α'‖ = 1 := by
    simp only [α', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    change r⁻¹*r = 1
    exact inv_mul_cancel₀ hr.ne'
  have hrα : r • α' = α := by simp only [α', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hrβ : r • β' = β := by simp only [β', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  obtain ⟨C, h₀, hC, hh₀, hc⟩ := system_four_unit_direction R hR α' β' hα' a v ha hv M V hM hV haM hvV
  refine ⟨(1+r)^2*C/r, r*h₀, by positivity, by positivity, fun h hh hhsmall U hU => ?_⟩
  have hh' : 0 < h/r := div_pos hh hr
  have hh'₀ : h/r ≤ h₀ := (div_le_iff₀ hr).2 (by nlinarith [hhsmall])
  have heh : r*(h/r) = h := by field_simp [hr.ne']
  have hl := sobNorm_hscale_one r (h/r) hr.le U
  rw [heh] at hl
  have ht := hc (h/r) hh' hh'₀ U hU
  have he := dirSystem_scale r (h/r) α' β' a v U
  rw [heh, hrα, hrβ] at he
  have hen : sobNorm (h/r) (-1) (dirSystem h α β a v U) =
      r^2*sobNorm (h/r) (-1) (dirSystem (h/r) α' β' a v U) := by
    rw [he, sobNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
  have hen' : sobNorm (h/r) (-1) (dirSystem (h/r) α' β' a v U) =
      sobNorm (h/r) (-1) (dirSystem h α β a v U)/r^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hr.ne')).2
    nlinarith only [hen]
  rw [hen'] at ht
  have ho := sobNorm_hscale_neg_one r (h/r) hr.le (dirSystem h α β a v U)
  rw [heh] at ho
  calc
    _ ≤ (1+r)*sobNorm (h/r) 1 U := hl
    _ ≤ (1+r)*((C/(h/r))*(sobNorm (h/r) (-1) (dirSystem h α β a v U)/r^2)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ (1+r)*((C/(h/r))*(((1+r)*sobNorm h (-1) (dirSystem h α β a v U))/r^2)) := by
      gcongr
    _ = _ := by field_simp [hr.ne', hh.ne']

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma dirDeriv_norm (h : ℝ) (hh : 0 ≤ h) (α β : X) (i : Fin 3) (f : S) :
    norm2 (dirDeriv h α β i f) ≤
      h*(1+‖((α i : ℂ)+Complex.I*(β i : ℂ))‖)*norm2 (J h 1 f) := by
  have hd := semideriv_bound h 1 hh i f
  norm_num only [sub_self, J_zero] at hd
  have hz := norm2_J_one_ge h f
  simp only [dirDeriv]
  calc
    _ ≤ norm2 (((h^2 : ℝ) : ℂ) • d (e i) f) +
        norm2 (((h : ℂ)*((α i : ℂ)+Complex.I*(β i : ℂ))) • f) := norm2_add_le _ _
    _ = h^2*norm2 (d (e i) f) +
        (h*‖((α i : ℂ)+Complex.I*(β i : ℂ))‖)*norm2 f := by
      simp only [norm2_const_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hh, abs_of_nonneg (sq_nonneg h)]
    _ ≤ h*norm2 (J h 1 f)+(h*‖((α i : ℂ)+Complex.I*(β i : ℂ))‖)*norm2 (J h 1 f) := by
      have hd' := mul_le_mul_of_nonneg_left hd hh
      have hz' := mul_le_mul_of_nonneg_left hz (mul_nonneg hh (norm_nonneg ((α i : ℂ)+Complex.I*(β i : ℂ))))
      nlinarith only [hd', hz']
    _ = _ := by ring

lemma lowerDir_norm (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (α β : X)
    (a : Fin 3 → X → ℂ) (v : X → ℂ)
    (ha : ∀ i,(a i).HasTemperateGrowth) (hv : v.HasTemperateGrowth)
    (A V Z : ℝ) (hA : 0≤A) (hV : 0≤V)
    (haA : ∀ i x,‖a i x‖≤A) (hvV : ∀ x,‖v x‖≤V)
    (hz : ∀ i,‖((α i : ℂ)+Complex.I*(β i : ℂ))‖≤Z) (f : S) :
    norm2 (lowerDir h α β a v f) ≤ (3*A*(1+Z)+V)*h*norm2 (J h 1 f) := by
  have hd (i : Fin 3) : norm2 (mult (a i) (dirDeriv h α β i f)) ≤
      A*(h*(1+Z)*norm2 (J h 1 f)) := by
    apply (norm2_mult (a i) (ha i) A (haA i) _).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply (dirDeriv_norm h hh α β i f).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_right (hz i) 1) hh) (norm2_nonneg _)
  have hs := norm2_sum_le Finset.univ (fun i : Fin 3 => mult (a i) (dirDeriv h α β i f))
  have hs' := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs'
  have hv' := norm2_mult v hv V hvV f
  have hn := norm2_J_one_ge h f
  have hsq : h^2≤h := by nlinarith
  have hv'' : h^2*norm2 (mult v f) ≤ h*V*norm2 (J h 1 f) := by
    calc
      _ ≤ h^2*(V*norm2 f) := mul_le_mul_of_nonneg_left hv' (sq_nonneg h)
      _ ≤ h*(V*norm2 (J h 1 f)) :=
        (mul_le_mul_of_nonneg_right hsq (mul_nonneg hV (norm2_nonneg _))).trans
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hV) hh)
      _ = _ := by ring
  have ht := norm2_add_le (∑ i : Fin 3,mult (a i) (dirDeriv h α β i f))
    (((h^2 : ℝ) : ℂ) • mult v f)
  rw [norm2_const_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg h)] at ht
  change norm2 ((∑ i : Fin 3,mult (a i) (dirDeriv h α β i f))+
    (((h^2 : ℝ) : ℂ) • mult v f))≤_
  nlinarith only [ht,hs,hs',hv'']

lemma system_difference_bound (h : ℝ) (hh : 0≤h) (hh1 : h≤1) (α β : X)
    (a b : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v w : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j,(a k i j).HasTemperateGrowth) (hb : ∀ k i j,(b k i j).HasTemperateGrowth)
    (hv : ∀ i j,(v i j).HasTemperateGrowth) (hw : ∀ i j,(w i j).HasTemperateGrowth)
    (A V Z : ℝ) (hA : 0≤A) (hV : 0≤V) (hZ : 0≤Z)
    (haA : ∀ k i j x,‖a k i j x‖≤A) (hbA : ∀ k i j x,‖b k i j x‖≤A)
    (hvV : ∀ i j x,‖v i j x‖≤V) (hwV : ∀ i j x,‖w i j x‖≤V)
    (hz : ∀ i,‖((α i : ℂ)+Complex.I*(β i : ℂ))‖≤Z) (U : Fin 4 → S) :
    sobNorm h (-1) (dirSystem h α β a v U-dirSystem h α β b w U) ≤
      16*(3*A*(1+Z)+V)*h*sobNorm h 1 U := by
  let K := (3*A*(1+Z)+V)*h
  have hK : 0≤K := by dsimp [K]; positivity
  have hi (i : Fin 4) : norm2 ((dirSystem h α β a v U-dirSystem h α β b w U) i) ≤
      2*K*sumNorm h 1 U := by
    have he : (dirSystem h α β a v U-dirSystem h α β b w U) i =
        (∑ j,lowerDir h α β (fun k => a k i j) (v i j) (U j))-
        (∑ j,lowerDir h α β (fun k => b k i j) (w i j) (U j)) := by
      simp only [Pi.sub_apply,dirSystem]; abel
    rw [he]
    have hn : ∀ f : S,norm2 (-f)=norm2 f := by intro f; simp only [norm2,map_neg,norm_neg]
    rw [sub_eq_add_neg]
    apply (norm2_add_le _ _).trans
    rw [hn]
    have h1 := (norm2_sum_le Finset.univ (fun j => lowerDir h α β (fun k => a k i j) (v i j) (U j))).trans
      (Finset.sum_le_sum (fun j _ => lowerDir_norm h hh hh1 α β (fun k => a k i j) (v i j)
        (fun k => ha k i j) (hv i j) A V Z hA hV (fun k => haA k i j) (hvV i j) hz (U j)))
    have h2 := (norm2_sum_le Finset.univ (fun j => lowerDir h α β (fun k => b k i j) (w i j) (U j))).trans
      (Finset.sum_le_sum (fun j _ => lowerDir_norm h hh hh1 α β (fun k => b k i j) (w i j)
        (fun k => hb k i j) (hw i j) A V Z hA hV (fun k => hbA k i j) (hwV i j) hz (U j)))
    simp only [← Finset.mul_sum] at h1 h2
    change _≤2*K*(∑ j,norm2 (J h 1 (U j)))
    dsimp [K]
    linarith only [h1,h2]
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (norm2_J_nonpos h (-1) (by norm_num) _).trans (hi i))
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hn
  apply (sobNorm_le_sumNorm h (-1) _).trans
  change sumNorm h (-1) _≤_
  apply hn.trans
  have hf := mul_le_mul_of_nonneg_left (sumNorm_four_le h 1 U) (by positivity : 0≤4*(2*K))
  dsimp [K] at hf
  nlinarith only [hf]

/-- The exact compact comparison estimate: the common second-order principal
part cancels, and the h factor in its actual lower-order forcing cancels the
Carleman 1/h loss. This dependency does not assert that the physical DN transfer
has already supplied the forcing identity. -/
theorem compact_comparison_estimate (R : ℝ) (hR : 1≤R) (α β : X) (hα : α≠0)
    (a b : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v w : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j,(a k i j).HasTemperateGrowth) (hb : ∀ k i j,(b k i j).HasTemperateGrowth)
    (hv : ∀ i j,(v i j).HasTemperateGrowth) (hw : ∀ i j,(w i j).HasTemperateGrowth)
    (A V Z : ℝ) (hA : 0≤A) (hV : 0≤V) (hZ : 0≤Z)
    (haA : ∀ k i j x,‖a k i j x‖≤A) (hbA : ∀ k i j x,‖b k i j x‖≤A)
    (hvV : ∀ i j x,‖v i j x‖≤V) (hwV : ∀ i j x,‖w i j x‖≤V)
    (hz : ∀ i,‖((α i : ℂ)+Complex.I*(β i : ℂ))‖≤Z) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∀ U W : Fin 4 → S,(∀ i,BallSupported R (W i)) →
      dirSystem h α β b w W=dirSystem h α β a v U-dirSystem h α β b w U →
      sobNorm h 1 W≤C*sobNorm h 1 U := by
  obtain ⟨C,h₀,hC,hh₀,hest⟩ := system_four_direction R hR α β hα b w hb hw A V hA hV hbA hwV
  let B := 16*(3*A*(1+Z)+V)
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨C*(1+B),min h₀ 1,by positivity,lt_min hh₀ zero_lt_one,fun h hh hsmall U W hW he => ?_⟩
  have h1 := hest h hh (hsmall.trans (min_le_left _ _)) W hW
  rw [he] at h1
  have h2 := system_difference_bound h hh.le (hsmall.trans (min_le_right _ _)) α β a b v w ha hb hv hw
    A V Z hA hV hZ haA hbA hvV hwV hz U
  calc
    _ ≤ (C/h)*sobNorm h (-1) (dirSystem h α β a v U-dirSystem h α β b w U) := h1
    _ ≤ (C/h)*(B*h*sobNorm h 1 U) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C*B*sobNorm h 1 U := by field_simp
    _ ≤ C*(1+B)*sobNorm h 1 U := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      gcongr
      linarith
end ElasticityPhysicalEstimate

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma toSmooth_injective : Function.Injective toSmooth := by
  intro f g h
  ext x
  exact congrArg (fun a : Smooth => (a : X → ℂ) x) h

lemma toSmooth_d (f : S) (i : Fin 3) :
    toSmooth (d (e i) f) = ElasticityAugmented.coord i (toSmooth f) := by
  apply Subtype.ext
  rfl

lemma toSmooth_mult (a : Smooth) (ha : (a : X → ℂ).HasTemperateGrowth) (f : S) :
    toSmooth (mult a f) = a*toSmooth f := by
  apply Subtype.ext
  funext x
  exact mult_apply a ha f x

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

lemma toSmooth_shiftD (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    toSmooth (shiftD z i f) = ElasticityAugmented.shifted ElasticityAugmented.coord z i (toSmooth f) := by
  simp only [shiftD_apply, map_add, map_smul, toSmooth_d, ElasticityAugmented.shifted_apply]

lemma toSmooth_physical (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (u : Fin 3 → S) (i : Fin 3) :
    toSmooth (physical z lam m u i) =
      ElasticityAugmented.LT (ElasticityAugmented.shifted ElasticityAugmented.coord z)
        lam m (fun j => toSmooth (u j)) i := by
  simp only [physical, ElasticityAugmented.LT, ElasticityAugmented.divT, map_add, map_sum,
    toSmooth_shiftD, toSmooth_mult lam hl, toSmooth_mult m hm,
    Finset.mul_sum, mul_add]

lemma dirDeriv_eq_shiftD (h : ℝ) (hh : h ≠ 0) (α β : X) (i : Fin 3) (f : S) :
    dirDeriv h α β i f = ((h^2 : ℝ) : ℂ) • shiftD (phase h α β) i f := by
  rw [dirDeriv, shiftD_apply, smul_add, smul_smul]
  congr 1
  congr 1
  simp only [phase]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp [hc]

lemma toSmooth_lapShift (z : Fin 3 → ℂ) (f : S) :
    toSmooth (lapShift z f) =
      ElasticityAugmented.lapT (ElasticityAugmented.shifted ElasticityAugmented.coord z) (toSmooth f) := by
  simp only [lapShift, ElasticityAugmented.lapT, map_sum, toSmooth_shiftD]

lemma toSmooth_divShift (z : Fin 3 → ℂ) (u : Fin 3 → S) :
    toSmooth (divShift z u) =
      ElasticityAugmented.divT (ElasticityAugmented.shifted ElasticityAugmented.coord z) (fun i => toSmooth (u i)) := by
  simp only [divShift, ElasticityAugmented.divT, map_sum, toSmooth_shiftD]

lemma Pdir_eq_lapShift (h : ℝ) (hh : h ≠ 0) (α β : X) (f : S) :
    Pdir h α β f = -((h^2 : ℝ) : ℂ) • lapShift (phase h α β) f := by
  ext x
  simp only [Pdir, lapShift, shiftD_apply, map_add, map_smul, lap_apply,
    d_sum_basis α f, d_sum_basis β f,
    EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_three, add_apply, sub_apply,
    smul_apply, smul_eq_mul, phase]
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp [hc]
  ring_nf
  simp only [Complex.I_sq]
  ring

end ElasticityPhysicalAlgebra

open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A) (T : Fin 3 → A →ₗ[ℂ] A)

lemma normalizedPair_matrix (lam m n o : A) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (U : Fin 4 → A) (i : Fin 4) :
    normalizedPair D T lam m n o (fun j => U j.succ) (U 0) i =
      lapT T (U i) + (∑ k, ∑ j, coeffA D lam m n o k i j * T k (U j)) +
        (∑ j, coeffV D lam m n o i j*U j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · change o*(ST D T lam m _ _-2*n*(∑ i, D i m*RT D T lam m _ _ i)) = _
    rw [normalized_scalar D T lam m n o hn ho]
    simp only [coeffA, coeffV, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
    ring
  · change n*RT D T lam m _ _ i = _
    rw [normalized_vector D T lam m n hn]
    simp only [coeffA, coeffV, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      zero_mul, Finset.sum_const_zero, add_zero, add_mul, ite_mul,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

end ElasticityAugmented

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology
namespace ElasticityPhysicalEstimate

section
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV normalizedPair shifted)

lemma toSmooth_aPhys (lam m n o : Smooth)
    (ha : ∀ k i j, ((coeffA coord lam m n o k i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (k : Fin 3) (i j : Fin 4) (f : S) :
    toSmooth (mult (aPhys lam m n o k i j) f) = -coeffA coord lam m n o k i j*toSmooth f := by
  exact toSmooth_mult (-coeffA coord lam m n o k i j) ((ha k i j).neg) f
lemma toSmooth_vPhys (lam m n o : Smooth)
    (hv : ∀ i j, ((coeffV coord lam m n o i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (i j : Fin 4) (f : S) :
    toSmooth (mult (vPhys lam m n o i j) f) = -coeffV coord lam m n o i j*toSmooth f := by
  exact toSmooth_mult (-coeffV coord lam m n o i j) ((hv i j).neg) f

lemma toSmooth_dirSystem (h : ℝ) (hh : h ≠ 0) (α β : X)
    (lam m n o : Smooth) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (ha : ∀ k i j, ((coeffA coord lam m n o k i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hv : ∀ i j, ((coeffV coord lam m n o i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (U : Fin 4 → S) (i : Fin 4) :
    toSmooth (dirSystem h α β (aPhys lam m n o) (vPhys lam m n o) U i) =
      -((h^2 : ℝ) : ℂ) • normalizedPair coord (shifted coord (phase h α β)) lam m n o
        (fun j => toSmooth (U j.succ)) (toSmooth (U 0)) i := by
  rw [ElasticityAugmented.normalizedPair_matrix coord _ lam m n o hn ho (fun j => toSmooth (U j)) i]
  simp only [dirSystem, lowerDir, Pdir_eq_lapShift h hh, dirDeriv_eq_shiftD h hh,
    map_add, map_sum, map_smul, toSmooth_shiftD,
    toSmooth_aPhys lam m n o ha, toSmooth_vPhys lam m n o hv,
    smul_add, Finset.smul_sum, neg_smul]
  simp only [map_neg, map_smul, toSmooth_lapShift, Fin.sum_univ_succ,
    Algebra.smul_def]
  ring

lemma toSmooth_forcing (h : ℝ) (hh : h ≠ 0) (α β : X)
    (m n o : Smooth)
    (hn : (n : X → ℂ).HasTemperateGrowth) (ho : (o : X → ℂ).HasTemperateGrowth)
    (hc : ∀ i, (cPhys m n i).HasTemperateGrowth)
    (F : Fin 3 → S) (i : Fin 4) :
    toSmooth (augmentedForcing h α β n o (cPhys m n) F i) =
      ((h^2 : ℝ) : ℂ) • Fin.cons (α := fun _ : Fin 4 => Smooth)
        (o*(ElasticityAugmented.divT (shifted coord (phase h α β)) (fun j => toSmooth (F j)) -
          2*n*(∑ j, coord j m*toSmooth (F j))))
        (fun j => n*toSmooth (F j)) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [augmentedForcing, Fin.cons_zero, map_sum, map_add, map_smul,
      dirDeriv_eq_shiftD h hh, toSmooth_mult o ho, toSmooth_shiftD]
    have hcm (j : Fin 3) : toSmooth (mult (cPhys m n j) (F j)) =
        (-2*n*coord j m)*toSmooth (F j) := toSmooth_mult _ (hc j) _
    simp only [hcm, ElasticityAugmented.divT, Fin.sum_univ_three, Algebra.smul_def]
    ring
  · simp only [augmentedForcing, Fin.cons_succ, map_smul, toSmooth_mult n hn]

lemma physical_system_identity (h : ℝ) (hh : h ≠ 0) (α β : X)
    (lam m n o : Smooth) (hinv : n*m=1) (hoinv : o*(lam+m+m)=1)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hn : (n : X → ℂ).HasTemperateGrowth) (ho : (o : X → ℂ).HasTemperateGrowth)
    (ha : ∀ k i j, ((coeffA coord lam m n o k i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hv : ∀ i j, ((coeffV coord lam m n o i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hc : ∀ i, (cPhys m n i).HasTemperateGrowth)
    (u : Fin 3 → S) :
    dirSystem h α β (aPhys lam m n o) (vPhys lam m n o)
        (Fin.cons (divShift (phase h α β) u) u) =
      fun i => -augmentedForcing h α β n o (cPhys m n) (physical (phase h α β) lam m u) i := by
  funext i
  apply toSmooth_injective
  rw [map_neg, toSmooth_dirSystem h hh α β lam m n o hinv hoinv ha hv,
    toSmooth_forcing h hh α β m n o hn ho hc]
  simp only [Fin.cons_zero, Fin.cons_succ, toSmooth_divShift,
    toSmooth_physical _ lam m hl hm, neg_smul]
  congr 1
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [normalizedPair, Fin.cons_zero]
    rw [ElasticityAugmented.shifted_physical_divergence coord _ _ _ _ ElasticityAugmented.coord_commute]
    simp only [ElasticityAugmented.shifted_physical_expansion coord _ _ _ _ ElasticityAugmented.coord_commute]
  · simp only [normalizedPair, Fin.cons_succ,
      ElasticityAugmented.shifted_physical_expansion coord _ _ _ _ ElasticityAugmented.coord_commute]

end

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)

lemma deriv_zero_on {B : Set X} (hB : IsOpen B) (f : S) (hf : EqOn (f : X → ℂ) 0 B)
    (v : X) : EqOn (d v f : X → ℂ) 0 B := by
  intro x hx
  have he : (f : X → ℂ)=ᶠ[𝓝 x] 0 := by
    filter_upwards [hB.mem_nhds hx] with y hy using hf hy
  change fderiv ℝ (f : X → ℂ) x v=0
  rw [he.fderiv_eq]
  simp only [fderiv_zero]
  rfl

lemma dirDeriv_zero_on {B : Set X} (hB : IsOpen B) (h : ℝ) (α β : X)
    (f : S) (hf : EqOn (f : X → ℂ) 0 B) (i : Fin 3) :
    EqOn (dirDeriv h α β i f : X → ℂ) 0 B := by
  intro x hx
  simp only [dirDeriv,add_apply,smul_apply,deriv_zero_on hB f hf (e i) hx,hf hx,
    smul_zero,add_zero,Pi.zero_apply]

/-- A local physical solution satisfies the actual normalized four-system,
including its scalar row, on the same open set. -/
theorem physical_dirSystem_on {B : Set X} (hB : IsOpen B)
    (h : ℝ) (hh : h≠0) (α β : X)
    (lam m n o : Smooth) (hinv : n*m=1) (hoinv : o*(lam+m+m)=1)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hn : (n : X → ℂ).HasTemperateGrowth) (ho : (o : X → ℂ).HasTemperateGrowth)
    (ha : ∀ k i j,((coeffA coord lam m n o k i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hv : ∀ i j,((coeffV coord lam m n o i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hc : ∀ i,(cPhys m n i).HasTemperateGrowth)
    (u : Fin 3 → S) (hu : ∀ i,EqOn (physical (phase h α β) lam m u i : X → ℂ) 0 B) :
    ∀ i,EqOn (dirSystem h α β (aPhys lam m n o) (vPhys lam m n o)
      (Fin.cons (divShift (phase h α β) u) u) i : X → ℂ) 0 B := by
  rw [physical_system_identity h hh α β lam m n o hinv hoinv hl hm hn ho ha hv hc u]
  intro i x hx
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [augmentedForcing,Fin.cons_zero,neg_apply,mult_apply _ ho,
      sum_apply,add_apply,smul_apply,mult_apply _ (hc _),
      dirDeriv_zero_on hB h α β _ (hu _) _ hx,hu _ hx,Pi.zero_apply,
      smul_zero,mul_zero,add_zero,Finset.sum_const_zero,neg_zero]
  · simp only [augmentedForcing,Fin.cons_succ,neg_apply,smul_apply,
      mult_apply _ hn,hu _ hx,Pi.zero_apply,mul_zero,smul_zero,neg_zero]

lemma dirSystem_sub (h : ℝ) (α β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (U W : Fin 4 → S) :
    dirSystem h α β a v (U-W)=dirSystem h α β a v U-dirSystem h α β a v W := by
  have hd (i : Fin 3) (f g : S) : dirDeriv h α β i (f-g)=dirDeriv h α β i f-dirDeriv h α β i g := by
    simp only [dirDeriv,map_sub,smul_sub]
    module
  have hl (a : Fin 3 → X → ℂ) (v : X → ℂ) (f g : S) :
      lowerDir h α β a v (f-g)=lowerDir h α β a v f-lowerDir h α β a v g := by
    simp only [lowerDir,hd,map_sub,smul_sub,Finset.sum_sub_distrib]
    abel
  have hp (f g : S) : Pdir h α β (f-g)=Pdir h α β f-Pdir h α β g := by
    simp only [Pdir,map_sub,smul_sub]
    module
  funext i
  simp only [dirSystem,Pi.sub_apply,hp,hl,Finset.sum_sub_distrib]
  abel

lemma deriv_supported {K : Set X} (f : S) (hf : tsupport (f : X → ℂ)⊆K) (v : X) :
    tsupport (d v f : X → ℂ)⊆K :=
  (tsupport_fderiv_apply_subset ℝ v).trans hf

lemma dirSystem_zero_outside {K : Set X} (h : ℝ) (α β : X)
    (a : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j,(a k i j).HasTemperateGrowth) (hv : ∀ i j,(v i j).HasTemperateGrowth)
    (W : Fin 4 → S) (hW : ∀ i,tsupport (W i : X → ℂ)⊆K) {x : X} (hx : x∉K) (i : Fin 4) :
    dirSystem h α β a v W i x=0 := by
  have hz (f : S) (hf : tsupport (f : X → ℂ)⊆K) : f x=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hf ht))
  have hd (i : Fin 4) (q : X) : d q (W i) x=0 := hz _ (deriv_supported _ (hW i) q)
  have hdd (i : Fin 4) (q r : X) : d q (d r (W i)) x=0 :=
    hz _ (deriv_supported _ (deriv_supported _ (hW i) r) q)
  simp only [dirSystem,Pdir,lowerDir,dirDeriv,lap_apply,
    add_apply,sub_apply,smul_apply,sum_apply,mult_apply _ (ha _ _ _),mult_apply _ (hv _ _),
    hd,hdd,hz _ (hW _),smul_zero,mul_zero,add_zero,sub_zero,Finset.sum_const_zero]

lemma dirSystem_difference_zero_outside {K : Set X} (h : ℝ) (α β : X)
    (a b : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v w : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j,(a k i j).HasTemperateGrowth) (hb : ∀ k i j,(b k i j).HasTemperateGrowth)
    (hv : ∀ i j,(v i j).HasTemperateGrowth) (hw : ∀ i j,(w i j).HasTemperateGrowth)
    (hea : ∀ k i j x,x∉K → a k i j x=b k i j x)
    (hev : ∀ i j x,x∉K → v i j x=w i j x)
    (U : Fin 4 → S) {x : X} (hx : x∉K) (i : Fin 4) :
    (dirSystem h α β a v U-dirSystem h α β b w U) i x=0 := by
  simp only [Pi.sub_apply,sub_apply,dirSystem,lowerDir,add_apply,sum_apply,smul_apply,
    mult_apply _ (ha _ _ _),mult_apply _ (hb _ _ _),mult_apply _ (hv _ _),mult_apply _ (hw _ _),
    hea _ _ _ x hx,hev _ _ x hx,sub_self]

/-- A genuine local pair of homogeneous normalized solutions with compact
supported difference has the global compact forcing identity used by Carleman.
Only equality of the lower-order coefficients off K is required; no artificial
second-order difference term is introduced. -/
theorem compact_forcing_identity {B K : Set X} (hKB : K⊆B) (h : ℝ) (α β : X)
    (a b : Fin 3 → Fin 4 → Fin 4 → X → ℂ) (v w : Fin 4 → Fin 4 → X → ℂ)
    (ha : ∀ k i j,(a k i j).HasTemperateGrowth) (hb : ∀ k i j,(b k i j).HasTemperateGrowth)
    (hv : ∀ i j,(v i j).HasTemperateGrowth) (hw : ∀ i j,(w i j).HasTemperateGrowth)
    (hea : ∀ k i j x,x∉K → a k i j x=b k i j x)
    (hev : ∀ i j x,x∉K → v i j x=w i j x)
    (U V : Fin 4 → S) (hs : ∀ i,tsupport ((V-U) i : X → ℂ)⊆K)
    (hU : ∀ i,EqOn (dirSystem h α β a v U i : X → ℂ) 0 B)
    (hV : ∀ i,EqOn (dirSystem h α β b w V i : X → ℂ) 0 B) :
    dirSystem h α β b w (V-U)=dirSystem h α β a v U-dirSystem h α β b w U := by
  funext i
  ext x
  by_cases hx : x∈K
  · rw [dirSystem_sub]
    simp only [Pi.sub_apply,sub_apply,hU i (hKB hx),hV i (hKB hx),Pi.zero_apply]
  · rw [dirSystem_zero_outside h α β b w hb hw (V-U) hs hx i,
      dirSystem_difference_zero_outside h α β a b v w ha hb hv hw hea hev U hx i]
end ElasticityPhysicalEstimate

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators
namespace ElasticityCoeffBounds
open ElasticityAugmented ElasticityPhysicalEstimate

lemma ExteriorConstant.bound {f : Smooth} (hf : ExteriorConstant f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(f : X → ℂ) x‖ ≤ C := by
  obtain ⟨c, hc⟩ := hf
  have hcont : Continuous (fun x => ‖(f : X → ℂ) x - c‖) :=
    ((smooth_coe f).continuous.sub continuous_const).norm
  obtain ⟨x₀, hx⟩ := hcont.exists_forall_ge_of_hasCompactSupport hc.norm
  refine ⟨‖(f : X → ℂ) x₀ - c‖ + ‖c‖, by positivity, fun x => ?_⟩
  calc
    ‖(f : X → ℂ) x‖ = ‖((f : X → ℂ) x-c)+c‖ := by rw [sub_add_cancel]
    _ ≤ ‖(f : X → ℂ) x-c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ ‖(f : X → ℂ) x₀-c‖ + ‖c‖ := by linarith [hx x]

lemma ExteriorConstant.const (c : ℂ) : ExteriorConstant (algebraMap ℂ Smooth c) := by
  refine ⟨c, ?_⟩
  change HasCompactSupport (fun _ : X => c-c)
  exact HasCompactSupport.intro isCompact_empty (fun _ _ => sub_self c)

lemma ExteriorConstant.add {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f+g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c+d, ?_⟩
  have he : (fun x => ((f+g : Smooth) : X → ℂ) x - (c+d)) =
      (fun x => (f : X → ℂ) x-c) + (fun x => (g : X → ℂ) x-d) := by
    funext x
    change (f : X → ℂ) x + (g : X → ℂ) x - (c+d) = _
    dsimp
    ring
  rw [he]
  exact hc.add hd

lemma ExteriorConstant.mul {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f*g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c*d, ?_⟩
  have h1 : HasCompactSupport ((fun x => (f : X → ℂ) x-c) * (g : X → ℂ)) := hc.mul_right
  have h2 : HasCompactSupport ((fun _ : X => c) * (fun x => (g : X → ℂ) x-d)) := hd.mul_left
  have he : (fun x => ((f*g : Smooth) : X → ℂ) x - c*d) =
      ((fun x => (f : X → ℂ) x-c) * (g : X → ℂ)) +
        ((fun _ : X => c) * (fun x => (g : X → ℂ) x-d)) := by
    funext x
    change (f : X → ℂ) x * (g : X → ℂ) x - c*d = _
    dsimp
    ring
  rw [he]
  exact h1.add h2

lemma ExteriorConstant.neg {f : Smooth} (hf : ExteriorConstant f) : ExteriorConstant (-f) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨-c, ?_⟩
  have he : (fun x => ((-f : Smooth) : X → ℂ) x - (-c)) = -(fun x => (f : X → ℂ) x-c) := by
    funext x
    change -(f : X → ℂ) x - (-c) = -((f : X → ℂ) x-c)
    ring
  rw [he]
  exact hc.neg

lemma ExteriorConstant.sub {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f-g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma ExteriorConstant.coord {f : Smooth} (hf : ExteriorConstant f) (i : Fin 3) :
    ExteriorConstant (coord i f) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨0, ?_⟩
  have hs : HasCompactSupport (fun x => fderiv ℝ (fun y => (f : X → ℂ) y-c) x (e i)) :=
    hc.fderiv_apply (𝕜 := ℝ) (e i)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [sub_zero, coord_apply, fderiv_sub_const]

lemma ExteriorConstant.zero : ExteriorConstant (0 : Smooth) := by
  simpa only [map_zero] using ExteriorConstant.const 0

lemma ExteriorConstant.natCast (n : ℕ) : ExteriorConstant (n : Smooth) := by
  simpa only [map_natCast] using ExteriorConstant.const (n : ℂ)

lemma ExteriorConstant.sum {ι : Type*} (s : Finset ι) (f : ι → Smooth)
    (hf : ∀ i ∈ s, ExteriorConstant (f i)) : ExteriorConstant (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using ExteriorConstant.zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma exterior_coeffA {lam m n o : Smooth} (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hn : ExteriorConstant n) (ho : ExteriorConstant o) (k : Fin 3) (i j : Fin 4) :
    ExteriorConstant (coeffA coord lam m n o k i j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact ((ExteriorConstant.natCast 2).mul ho).mul
        (((hl.add hm).coord k).sub (((hl.add hm).mul hn).mul (hm.coord k)))
    · exact ((ExteriorConstant.natCast 2).mul ho).mul
        (((hm.coord j).coord k).sub
          ((((ExteriorConstant.natCast 2).mul hn).mul (hm.coord k)).mul (hm.coord j)))
  · refine Fin.cases ?_ (fun j => ?_) j
    · change ExteriorConstant (if k=i then (lam+m)*n else 0)
      split
      · exact (hl.add hm).mul hn
      · exact ExteriorConstant.zero
    · change ExteriorConstant ((if j=i then n*coord k m else 0) +
        (if k=i then n*coord j m else 0))
      apply ExteriorConstant.add
      · split
        · exact hn.mul (hm.coord k)
        · exact ExteriorConstant.zero
      · split
        · exact hn.mul (hm.coord j)
        · exact ExteriorConstant.zero

lemma exterior_coeffV {lam m n o : Smooth} (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hn : ExteriorConstant n) (ho : ExteriorConstant o) (i j : Fin 4) :
    ExteriorConstant (coeffV coord lam m n o i j) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun _ => ExteriorConstant.zero) j
    exact ho.mul ((ExteriorConstant.sum Finset.univ _ (fun i _ => (hl.coord i).coord i)).sub
      (((ExteriorConstant.natCast 2).mul hn).mul
        (ExteriorConstant.sum Finset.univ _ (fun i _ => (hm.coord i).mul (hl.coord i)))))
  · refine Fin.cases ?_ (fun _ => ExteriorConstant.zero) j
    exact hn.mul (hl.coord i)

lemma exterior_cPhys {m n : Smooth} (hm : ExteriorConstant m) (hn : ExteriorConstant n)
    (i : Fin 3) : ExteriorConstant (-2*n*coord i m) :=
  (((ExteriorConstant.natCast 2).neg).mul hn).mul (hm.coord i)

lemma ExteriorConstant.uniform_bound {ι : Type*} [Fintype ι] (f : ι → Smooth)
    (hf : ∀ i, ExteriorConstant (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖(f i : X → ℂ) x‖ ≤ C := by
  classical
  choose C hC hb using (fun i => (hf i).bound)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i x => ?_⟩
  exact (hb i x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

lemma reciprocal_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) :
    reciprocal f hf * f = 1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra (physical phase)

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented

lemma restrict_coeffA {B : Set X} (hB : IsOpen B) (lam m n o : Smooth)
    (k : Fin 3) (i j : Fin 4) :
    restrictSmooth B (coeffA coord lam m n o k i j)=
      coeffA (localCoord hB) (restrictSmooth B lam) (restrictSmooth B m)
        (restrictSmooth B n) (restrictSmooth B o) k i j := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffA,Fin.cons_zero,Fin.cons_succ,map_mul,map_add,map_sub,map_ofNat,
      localCoord_restrict,map_zero,apply_ite] <;> split_ifs <;> rfl

lemma restrict_coeffV {B : Set X} (hB : IsOpen B) (lam m n o : Smooth)
    (i j : Fin 4) :
    restrictSmooth B (coeffV coord lam m n o i j)=
      coeffV (localCoord hB) (restrictSmooth B lam) (restrictSmooth B m)
        (restrictSmooth B n) (restrictSmooth B o) i j := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffV,Fin.cons_zero,Fin.cons_succ,lap,map_mul,map_sub,map_ofNat,
      map_sum,localCoord_restrict,map_zero]

lemma inverse_eqOn {B : Set X} (m₁ m₂ n₁ n₂ : Smooth)
    (hn₁ : n₁*m₁=1) (hn₂ : n₂*m₂=1) (he : EqOn (m₁ : X → ℂ) m₂ B) :
    EqOn (n₁ : X → ℂ) n₂ B := by
  intro x hx
  have h1 := congrArg (fun f : Smooth => (f : X → ℂ) x) hn₁
  have h2 := congrArg (fun f : Smooth => (f : X → ℂ) x) hn₂
  change (n₁ : X → ℂ) x*(m₁ : X → ℂ) x=1 at h1
  change (n₂ : X → ℂ) x*(m₂ : X → ℂ) x=1 at h2
  rw [he hx] at h1
  linear_combination (n₂ : X → ℂ) x*h1-(n₁ : X → ℂ) x*h2

/-- Equality of the original coefficients on an open set gives equality of
both actual normalized matrices there. Reciprocals are not extra exterior
identifications: they follow from their defining inverse identities. -/
theorem normalized_coefficients_eqOn {B : Set X} (hB : IsOpen B)
    (l₁ m₁ n₁ o₁ l₂ m₂ n₂ o₂ : Smooth)
    (hn₁ : n₁*m₁=1) (hn₂ : n₂*m₂=1)
    (ho₁ : o₁*(l₁+m₁+m₁)=1) (ho₂ : o₂*(l₂+m₂+m₂)=1)
    (hel : EqOn (l₁ : X → ℂ) l₂ B) (hem : EqOn (m₁ : X → ℂ) m₂ B) :
    (∀ k i j,EqOn ((coeffA coord l₁ m₁ n₁ o₁ k i j : Smooth) : X → ℂ)
      ((coeffA coord l₂ m₂ n₂ o₂ k i j : Smooth) : X → ℂ) B) ∧
    (∀ i j,EqOn ((coeffV coord l₁ m₁ n₁ o₁ i j : Smooth) : X → ℂ)
      ((coeffV coord l₂ m₂ n₂ o₂ i j : Smooth) : X → ℂ) B) := by
  have hen := inverse_eqOn m₁ m₂ n₁ n₂ hn₁ hn₂ hem
  have heo : EqOn (o₁ : X → ℂ) o₂ B :=
    inverse_eqOn _ _ o₁ o₂ ho₁ ho₂ (by
      intro x hx
      change (l₁ : X → ℂ) x+(m₁ : X → ℂ) x+(m₁ : X → ℂ) x =
        (l₂ : X → ℂ) x+(m₂ : X → ℂ) x+(m₂ : X → ℂ) x
      rw [hel hx,hem hx])
  have hl := (restrictSmooth_eq_iff B _ _).mpr hel
  have hm := (restrictSmooth_eq_iff B _ _).mpr hem
  have hn := (restrictSmooth_eq_iff B _ _).mpr hen
  have ho := (restrictSmooth_eq_iff B _ _).mpr heo
  constructor
  · intro k i j
    apply (restrictSmooth_eq_iff B _ _).mp
    rw [restrict_coeffA hB,restrict_coeffA hB,hl,hm,hn,ho]
  · intro i j
    apply (restrictSmooth_eq_iff B _ _).mp
    rw [restrict_coeffV hB,restrict_coeffV hB,hl,hm,hn,ho]
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (physical divShift shiftD shiftD_apply)
open ElasticityCarleman (phaseCLM)

/-- The actual shifted divergence of the compact physical difference also has
compact support; no separate scalar field is introduced. -/
lemma divShift_supported {K : Set X} (hK : IsClosed K) (z : Fin 3 → ℂ)
    (u : Fin 3 → S) (hu : ∀ i,tsupport (u i : X → ℂ)⊆K) :
    tsupport (divShift z u : X → ℂ)⊆K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hnot
  apply hx
  have hh (i : Fin 3) : u i x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hnot (hu i ht))
  have hd (i : Fin 3) : ElasticitySchwartzCarleman.d (e i) (u i) x=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    exact hnot (hu i ((tsupport_fderiv_apply_subset ℝ (e i)) ht))
  simp only [divShift,sum_apply,shiftD_apply,add_apply,
    smul_apply,hh,smul_zero,add_zero]
  change (∑ i, ElasticitySchwartzCarleman.d (e i) (u i) x)=0
  simp only [hd,Finset.sum_const_zero]
end ElasticityCGO

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)
open ElasticityCoeffBounds

lemma physicalAug_sub (z : Fin 3 → ℂ) (u v : Fin 3 → S) :
    physicalAug z (v-u)=physicalAug z v-physicalAug z u := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [physicalAug,Fin.cons_zero,Pi.sub_apply,divShift,map_sub,Finset.sum_sub_distrib]
  · rfl

lemma physicalAug_supported {K : Set X} (hK : IsClosed K) (z : Fin 3 → ℂ)
    (u : Fin 3 → S) (hu : ∀ i,tsupport (u i : X → ℂ)⊆K) :
    ∀ i,tsupport (physicalAug z u i : X → ℂ)⊆K := by
  intro i
  refine Fin.cases ?_ (fun i => hu i) i
  exact ElasticityCGO.divShift_supported hK z u hu

theorem physical_compact_comparison_oai {B K : Set X} (hB : IsOpen B)
    (hK : IsClosed K) (hKB : K⊆B) (R : ℝ) (hR : 1≤R)
    (hKR : K⊆Metric.closedBall 0 R) (α β : X) (hα : α≠0)
    (lam m : Fin 2 → Smooth)
    (hl : ∀ q,ExteriorConstant (lam q)) (hm : ∀ q,ExteriorConstant (m q))
    (hm0 : ∀ q x,(m q : X → ℂ) x≠0)
    (he0 : ∀ q x,((lam q+m q+m q : Smooth) : X → ℂ) x≠0)
    (hel : EqOn (lam 0 : X → ℂ) (lam 1) Kᶜ)
    (hem : EqOn (m 0 : X → ℂ) (m 1) Kᶜ) :
    ∃ C h₀ : ℝ,0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∀ u v : Fin 3 → S,
      (∀ i,tsupport ((v-u) i : X → ℂ)⊆K) →
      (∀ i,EqOn (physical (phase h α β) (lam 0) (m 0) u i : X → ℂ) 0 B) →
      (∀ i,EqOn (physical (phase h α β) (lam 1) (m 1) v i : X → ℂ) 0 B) →
      sobNorm h 1 (physicalAug (phase h α β) (v-u)) ≤
        C*sobNorm h 1 (physicalAug (phase h α β) u) := by
  let n := fun q => reciprocal (m q) (hm0 q)
  let o := fun q => reciprocal (lam q+m q+m q) (he0 q)
  have hn (q) : ExteriorConstant (n q) := (hm q).reciprocal (hm0 q)
  have ho (q) : ExteriorConstant (o q) := (((hl q).add (hm q)).add (hm q)).reciprocal (he0 q)
  have hni (q) : n q*m q=1 := reciprocal_mul _ _
  have hoi (q) : o q*(lam q+m q+m q)=1 := reciprocal_mul _ _
  have ha (q) := exterior_coeffA (hl q) (hm q) (hn q) (ho q)
  have hv (q) := exterior_coeffV (hl q) (hm q) (hn q) (ho q)
  have hc (q) := exterior_cPhys (hm q) (hn q)
  let a := fun q => aPhys (lam q) (m q) (n q) (o q)
  let w := fun q => vPhys (lam q) (m q) (n q) (o q)
  have hag (q k i j) : (a q k i j).HasTemperateGrowth := (ha q k i j).growth.neg
  have hwg (q i j) : (w q i j).HasTemperateGrowth := (hv q i j).growth.neg
  obtain ⟨A,hA,hba⟩ := ExteriorConstant.uniform_bound
    (fun t : Fin 2 × Fin 3 × Fin 4 × Fin 4 =>
      coeffA coord (lam t.1) (m t.1) (n t.1) (o t.1) t.2.1 t.2.2.1 t.2.2.2)
    (fun t => ha t.1 t.2.1 t.2.2.1 t.2.2.2)
  obtain ⟨V,hV,hbv⟩ := ExteriorConstant.uniform_bound
    (fun t : Fin 2 × Fin 4 × Fin 4 =>
      coeffV coord (lam t.1) (m t.1) (n t.1) (o t.1) t.2.1 t.2.2)
    (fun t => hv t.1 t.2.1 t.2.2)
  have hba' (q k i j x) : ‖a q k i j x‖≤A := by
    simpa only [a,aPhys,Pi.neg_apply,norm_neg] using hba (q,k,i,j) x
  have hbw' (q i j x) : ‖w q i j x‖≤V := by
    simpa only [w,vPhys,Pi.neg_apply,norm_neg] using hbv (q,i,j) x
  let Z := ∑ i,‖((α i : ℂ)+Complex.I*(β i : ℂ))‖
  have hZ : 0≤Z := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hz (i : Fin 3) : ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖≤Z :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((α j : ℂ)+Complex.I*(β j : ℂ))) (Finset.mem_univ i)
  obtain ⟨C,h₀,hC,hh₀,hest⟩ := compact_comparison_estimate R hR α β hα
    (a 0) (a 1) (w 0) (w 1) (hag 0) (hag 1) (hwg 0) (hwg 1)
    A V Z hA hV hZ (hba' 0) (hba' 1) (hbw' 0) (hbw' 1) hz
  obtain ⟨hea,hev⟩ := ElasticityAugmented.normalized_coefficients_eqOn hK.isOpen_compl
    (lam 0) (m 0) (n 0) (o 0) (lam 1) (m 1) (n 1) (o 1)
    (hni 0) (hni 1) (hoi 0) (hoi 1) hel hem
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall u v hs hu hv' => ?_⟩
  have hs' := physicalAug_supported hK (phase h α β) (v-u) hs
  have hlocal (q) (f : Fin 3 → S)
      (hf : ∀ i,EqOn (physical (phase h α β) (lam q) (m q) f i : X → ℂ) 0 B) :=
    physical_dirSystem_on hB h hh.ne' α β (lam q) (m q) (n q) (o q)
      (hni q) (hoi q) (hl q).growth (hm q).growth (hn q).growth (ho q).growth
      (fun k i j => (ha q k i j).growth) (fun i j => (hv q i j).growth)
      (fun i => (hc q i).growth) f hf
  rw [physicalAug_sub] at hs' ⊢
  refine hest h hh hsmall _ _ (fun i => ?_) ?_
  · intro x hx
    have ht := hKR (hs' i (subset_tsupport _ hx))
    simpa only [Metric.mem_closedBall,dist_zero_right] using ht
  · apply compact_forcing_identity hKB h α β (a 0) (a 1) (w 0) (w 1)
      (hag 0) (hag 1) (hwg 0) (hwg 1) _ _ _ _ hs' (hlocal 0 u hu) (hlocal 1 v hv')
    · intro k i j x hx
      exact congrArg Neg.neg (hea k i j hx)
    · intro i j x hx
      exact congrArg Neg.neg (hev i j hx)
end ElasticityPhysicalEstimate

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityPhysicalEstimate.physical_compact_comparison_oai := @OAI.ElasticityPhysicalEstimate.physical_compact_comparison_oai
