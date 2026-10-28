-- Prove2me | solution 1 for OAI.ElasticityDistribution.weak_smooth_solvability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:44:56.690345+00:00
-- url     : https://prove2.me/submissions/17c70bd7-eb84-462c-8b07-c0d7bfd06d21

import Mathlib
import Definitions.Def_OAIQ6El006

section
-- module Solutions.OAIQ6_Elast.Compat
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

lemma J_sum {ι : Type*} (T : Finset ι) (h s : ℝ) (f : ι → S) :
    J h s (∑ i ∈ T, f i) = ∑ i ∈ T, J h s (f i) := by
  simp only [J, FourierTransform.fourier_sum, map_sum, FourierTransform.fourierInv_sum]

lemma negNorm_sum_le {ι : Type*} (T : Finset ι) (h : ℝ) (f : ι → S) :
    norm2 (J h (-1) (∑ i ∈ T, f i)) ≤ ∑ i ∈ T, norm2 (J h (-1) (f i)) := by
  rw [J_sum]
  exact norm2_sum_le _ _

lemma sumNorm_three_le (h s : ℝ) (U : Fin 3 → S) :
    sumNorm h s U ≤ 2*sobNorm h s U := by
  have hn : 0 ≤ ∑ i, norm2 (J h s (U i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have ht := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i => norm2 (J h s (U i)))
  norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at ht
  dsimp only [sobNorm, sumNorm]
  nlinarith only [hs, ht, hn, Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2)]

lemma dirDeriv_negNorm (h : ℝ) (hh : 0 ≤ h) (α β : X) (i : Fin 3) (f : S) :
    norm2 (J h (-1) (dirDeriv h α β i f)) ≤
      h*(1+‖((α i : ℂ)+Complex.I*(β i : ℂ))‖)*norm2 f := by
  have hd := semideriv_bound h 0 hh i f
  norm_num only [zero_sub, J_zero] at hd
  have hz := norm2_J_nonpos h (-1) (by norm_num) f
  have hn := norm2_nonneg f
  simp only [dirDeriv, J_add, J_smul]
  calc
    _ ≤ norm2 (((h^2 : ℝ) : ℂ) • J h (-1) (d (e i) f)) +
        norm2 (((h : ℂ)*((α i : ℂ)+Complex.I*(β i : ℂ))) • J h (-1) f) := norm2_add_le _ _
    _ = h^2*norm2 (J h (-1) (d (e i) f)) +
        (h*‖((α i : ℂ)+Complex.I*(β i : ℂ))‖)*norm2 (J h (-1) f) := by
      simp only [norm2_const_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hh, abs_of_nonneg (sq_nonneg h)]
    _ ≤ h*norm2 f+(h*‖((α i : ℂ)+Complex.I*(β i : ℂ))‖)*norm2 f := by
      have hd' := mul_le_mul_of_nonneg_left hd hh
      have hz' := mul_le_mul_of_nonneg_left hz (mul_nonneg hh (norm_nonneg ((α i : ℂ)+Complex.I*(β i : ℂ))))
      nlinarith only [hd', hz']
    _ = _ := by ring

lemma forcing_bound (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (α β : X)
    (n o : X → ℂ) (c : Fin 3 → X → ℂ)
    (hn : n.HasTemperateGrowth) (ho : o.HasTemperateGrowth)
    (hc : ∀ i, (c i).HasTemperateGrowth)
    (A D Z : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hnA : ∀ x, ‖n x‖ ≤ A) (hoA : ∀ x, ‖o x‖ ≤ A)
    (hcA : ∀ i x, ‖c i x‖ ≤ A)
    (hod : ∀ x i, h*‖fderiv ℝ o x (e i)‖ ≤ D)
    (hz : ∀ i, ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖ ≤ Z)
    (F : Fin 3 → S) :
    sobNorm h (-1) (augmentedForcing h α β n o c F) ≤
      2*(A+3*(A+D)*(1+Z+A))*h*sobNorm h 0 F := by
  have hM : 0 ≤ 3*(A+D) := by positivity
  have hm (i : Fin 3) : norm2 (J h (-1) (((h^2 : ℝ) : ℂ) • mult (c i) (F i))) ≤
      h*A*norm2 (F i) := by
    rw [J_smul, norm2_const_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg h)]
    calc
      _ ≤ h^2*norm2 (mult (c i) (F i)) :=
        mul_le_mul_of_nonneg_left (norm2_J_nonpos _ _ (by norm_num) _) (sq_nonneg h)
      _ ≤ h^2*(A*norm2 (F i)) :=
        mul_le_mul_of_nonneg_left (norm2_mult _ (hc i) A (hcA i) _) (sq_nonneg h)
      _ ≤ h*A*norm2 (F i) := by
        have ht : h^2 ≤ h := by nlinarith only [hh, hh1]
        nlinarith [mul_le_mul_of_nonneg_right ht (mul_nonneg hA (norm2_nonneg (F i)))]
  have hd (i : Fin 3) : norm2 (J h (-1) (dirDeriv h α β i (F i))) ≤
      h*(1+Z)*norm2 (F i) := by
    exact (dirDeriv_negNorm h hh α β i _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show 1+‖((α i : ℂ)+Complex.I*(β i : ℂ))‖ ≤ 1+Z by linarith [hz i]) hh)
        (norm2_nonneg (F i)))
  have hs : norm2 (J h (-1) (augmentedForcing h α β n o c F 0)) ≤
      3*(A+D)*h*(1+Z+A)*sumNorm h 0 F := by
    change norm2 (J h (-1) (mult o _)) ≤ _
    calc
      _ ≤ 3*(A+D)*norm2 (J h (-1) (∑ i, (dirDeriv h α β i (F i) +
          ((h^2 : ℝ) : ℂ) • mult (c i) (F i)))) := mult_Hneg1 h hh o ho A D hA hD hoA hod _
      _ ≤ 3*(A+D)*(∑ i, norm2 (J h (-1) (dirDeriv h α β i (F i) +
          ((h^2 : ℝ) : ℂ) • mult (c i) (F i)))) :=
        mul_le_mul_of_nonneg_left (negNorm_sum_le Finset.univ h _) hM
      _ ≤ 3*(A+D)*(∑ i, h*(1+Z+A)*norm2 (F i)) := by
        gcongr with i
        rw [J_add]
        exact (norm2_add_le _ _).trans (by nlinarith only [hd i, hm i])
      _ = _ := by simp only [sumNorm, J_zero, ← Finset.mul_sum]; ring
  have ht (i : Fin 3) : norm2 (J h (-1) (augmentedForcing h α β n o c F i.succ)) ≤
      h*A*norm2 (F i) := by
    change norm2 (J h (-1) (((h^2 : ℝ) : ℂ) • mult n (F i))) ≤ _
    rw [J_smul, norm2_const_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg h)]
    calc
      _ ≤ h^2*norm2 (mult n (F i)) :=
        mul_le_mul_of_nonneg_left (norm2_J_nonpos _ _ (by norm_num) _) (sq_nonneg h)
      _ ≤ h^2*(A*norm2 (F i)) :=
        mul_le_mul_of_nonneg_left (norm2_mult _ hn A hnA _) (sq_nonneg h)
      _ ≤ h*A*norm2 (F i) := by
        have ht : h^2 ≤ h := by nlinarith only [hh, hh1]
        nlinarith [mul_le_mul_of_nonneg_right ht (mul_nonneg hA (norm2_nonneg (F i)))]
  calc
    _ ≤ sumNorm h (-1) (augmentedForcing h α β n o c F) := sobNorm_le_sumNorm _ _ _
    _ ≤ (A+3*(A+D)*(1+Z+A))*h*sumNorm h 0 F := by
      rw [sumNorm, Fin.sum_univ_succ]
      have hts := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ht i)
      simp only [← Finset.mul_sum] at hts
      have hsum : (∑ i, norm2 (F i)) = sumNorm h 0 F := by simp only [sumNorm, J_zero]
      rw [hsum] at hts
      nlinarith only [hs, hts]
    _ ≤ (A+3*(A+D)*(1+Z+A))*h*(2*sobNorm h 0 F) := by
      gcongr
      exact sumNorm_three_le _ _ _
    _ = _ := by ring

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

lemma shiftD_supported (z : Fin 3 → ℂ) (i : Fin 3) {R : ℝ} {f : S}
    (hf : BallSupported R f) : BallSupported R (shiftD z i f) :=
  (hf.d _).add (hf.smul _)

lemma divShift_supported (z : Fin 3 → ℂ) {R : ℝ} (u : Fin 3 → S)
    (hu : ∀ i, BallSupported R (u i)) : BallSupported R (divShift z u) := by
  exact BallSupported.sum _ _ (fun i _ => shiftD_supported z i (hu i))

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

lemma aPhys_growth (lam m n o : Smooth)
    (ha : ∀ k i j, ((coeffA coord lam m n o k i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (k : Fin 3) (i j : Fin 4) : (aPhys lam m n o k i j).HasTemperateGrowth :=
  (ha k i j).neg
lemma vPhys_growth (lam m n o : Smooth)
    (hv : ∀ i j, ((coeffV coord lam m n o i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (i j : Fin 4) : (vPhys lam m n o i j).HasTemperateGrowth :=
  (hv i j).neg

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

lemma norm_tail_le (h : ℝ) (b : S) (u : Fin 3 → S) :
    sobNorm h 0 u ≤ sobNorm h 1 (Fin.cons b u) := by
  unfold sobNorm
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_succ]
  simp only [J_zero]
  exact (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    pow_le_pow_left₀ (norm2_nonneg (u i)) (norm2_J_one_ge h (u i)) 2)).trans
      (le_add_of_nonneg_left (sq_nonneg _))

/-- The physical adjoint-test estimate obtained from the actual scalar-principal
augmented operator. All coefficients and forcing terms are explicit. -/
theorem physical_test_estimate (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (lam m n o : Smooth) (hinv : n*m=1) (hoinv : o*(lam+m+m)=1)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hn : (n : X → ℂ).HasTemperateGrowth) (ho : (o : X → ℂ).HasTemperateGrowth)
    (ha : ∀ k i j, ((coeffA coord lam m n o k i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hv : ∀ i j, ((coeffV coord lam m n o i j : Smooth) : X → ℂ).HasTemperateGrowth)
    (hc : ∀ i, (cPhys m n i).HasTemperateGrowth)
    (M V A D Z : ℝ) (hM : 0 ≤ M) (hV : 0 ≤ V) (hA : 0 ≤ A) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (haM : ∀ k i j x, ‖aPhys lam m n o k i j x‖ ≤ M)
    (hvV : ∀ i j x, ‖vPhys lam m n o i j x‖ ≤ V)
    (hnA : ∀ x, ‖(n : X → ℂ) x‖ ≤ A) (hoA : ∀ x, ‖(o : X → ℂ) x‖ ≤ A)
    (hcA : ∀ i x, ‖cPhys m n i x‖ ≤ A)
    (hod : ∀ x i, ‖fderiv ℝ (o : X → ℂ) x (e i)‖ ≤ D)
    (hz : ∀ i, ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖ ≤ Z) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ u : Fin 3 → S, (∀ i, BallSupported R (u i)) →
        sobNorm h 0 u ≤ C*sobNorm h 0 (physical (phase h α β) lam m u) := by
  obtain ⟨C, h₀, hC, hh₀, hest⟩ := system_four_direction R hR α β hα
    (aPhys lam m n o) (vPhys lam m n o) (aPhys_growth lam m n o ha)
    (vPhys_growth lam m n o hv) M V hM hV haM hvV
  let K := 2*(A+3*(A+D)*(1+Z+A))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C*(1+K), min h₀ 1, mul_pos hC (by positivity), lt_min hh₀ zero_lt_one, ?_⟩
  intro h hh hsmall u hu
  have hs0 := (le_min_iff.mp hsmall).1
  have hs1 := (le_min_iff.mp hsmall).2
  let F := physical (phase h α β) lam m u
  have hb := forcing_bound h hh.le hs1 α β n o (cPhys m n) hn ho hc A D Z hA hD hZ hnA hoA hcA
    (fun x i => (mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)).trans (by simpa using hod x i)) hz F
  have hu' : ∀ i, BallSupported R (Fin.cons (α := fun _ : Fin 4 => S) (divShift (phase h α β) u) u i) := by
    intro i
    exact Fin.cases (divShift_supported _ u hu) hu i
  have huest := hest h hh hs0 (Fin.cons (divShift (phase h α β) u) u) hu'
  rw [physical_system_identity h hh.ne' α β lam m n o hinv hoinv hl hm hn ho ha hv hc u] at huest
  have hneg : sobNorm h (-1) (fun i => -augmentedForcing h α β n o (cPhys m n) F i) =
      sobNorm h (-1) (augmentedForcing h α β n o (cPhys m n) F) := by
    simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using
      sobNorm_smul h (-1) (-1 : ℂ) (augmentedForcing h α β n o (cPhys m n) F)
  change sobNorm h 1 (Fin.cons (divShift (phase h α β) u) u) ≤
    (C/h)*sobNorm h (-1) (fun i => -augmentedForcing h α β n o (cPhys m n) F i) at huest
  rw [hneg] at huest
  calc
    _ ≤ sobNorm h 1 (Fin.cons (divShift (phase h α β) u) u) := norm_tail_le h _ u
    _ ≤ (C/h)*sobNorm h (-1) (augmentedForcing h α β n o (cPhys m n) F) := huest
    _ ≤ (C/h)*(K*h*sobNorm h 0 F) := mul_le_mul_of_nonneg_left hb (div_nonneg hC.le hh.le)
    _ = C*K*sobNorm h 0 F := by field_simp
    _ ≤ C*(1+K)*sobNorm h 0 F :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : K ≤ 1+K) hC.le)
        (Real.sqrt_nonneg _)

end

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)

end ElasticityPhysicalEstimate

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g+h) u=fourierMultiplierCLM F g u+fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply,smulLeftCLM_add hg hh,add_apply,fourierInv_add]

omit [CompleteSpace F] in
lemma besselPotential_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u=u+fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have he : (fun x : E => (((1+‖x‖^2)^(2/2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ))+(fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    funext x
    norm_num
  rw [besselPotential,he,fourierMultiplier_add (by fun_prop) (by fun_prop)]
  simp

lemma sobolev_real_smul {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (c : ℝ) :
    MemSobolev s 2 (c • u) := by
  convert hu.smul (c : ℂ) using 1
  all_goals try with_reducible_and_instances rfl

/-- Whole-space elliptic gain for the actual distributional Laplacian. -/
theorem laplacian_gain {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hm := sobolev_real_smul hΔ (-(2*Real.pi)^2)⁻¹
  rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul] at hm
  have h := hu.add hm
  rw [← besselPotential_two,memSobolev_besselPotential_iff] at h
  simpa only [add_comm] using h

/-- One derivative of gain from information on all coordinate first derivatives. -/
theorem coordinate_derivative_gain {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hall : ∀ S : Finset ι, MemSobolev (s-1) 2 (∑ i ∈ S, ∂_{b i} (∂_{b i} u)) := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS =>
      rw [Finset.sum_insert hi]
      exact ((hd i).lineDerivOp).add hS
  have hsum := hall Finset.univ
  rw [← laplacian_eq_sum b] at hsum
  have h := laplacian_gain (hu.mono (by linarith : s-1 ≤ s)) hsum
  have he : s-1+2=s+1 := by ring
  rwa [he] at h

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma compact_derivative {g : E → ℂ} (hg : HasCompactSupport g) (m : E) :
    HasCompactSupport (fun x => fderiv ℝ g x m) :=
  (hg.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T m) (by simp)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma smooth_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x m) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma sobolev_zero_product {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hb : MemLp g ∞ (volume : Measure E)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨v,rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨hb.toLp g • v, (Lp.toTemperedDistribution_smul_eq hg hb v).symm⟩

/-- Smooth compact coefficients preserve every nonnegative integral Sobolev order.
This is proved for the actual tempered distribution product, not an assumed
bounded multiplier on an unspecified Sobolev completion. -/
theorem sobolev_nat_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (n : ℕ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing u g with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    apply coordinate_derivative_gain b (ih hg hc (hu.mono (by norm_num)))
    intro i
    have hd : MemSobolev (n : ℝ) 2 (∂_{b i} u) := by
      simpa only [add_sub_cancel_right] using hu.lineDerivOp (m := b i)
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) (b i)
      ((compact_derivative hc (b i)).hasTemperateGrowth (smooth_derivative hg (b i)))]
    exact (ih (smooth_derivative hg (b i)) (compact_derivative hc (b i))
      (hu.mono (by norm_num))).add (ih hg hc hd)

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma eval_smooth (a : Coeff) : ContDiff ℝ (⊤ : ℕ∞) (eval a) := (growth a).1

lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl
lemma dc_commute (i j : Fin 3) (a : Coeff) : dc i (dc j a) = dc j (dc i a) := by
  apply Subtype.ext
  exact coord_commute i j a.val
lemma dd_commute (i j : Fin 3) (u : Dist) : dd i (dd j u) = dd j (dd i u) := by
  ext φ
  change u (- ∂_{e j} (- ∂_{e i} φ)) = u (- ∂_{e i} (- ∂_{e j} φ))
  simp only [LineDeriv.lineDerivOp_neg,neg_neg]
  congr 1
  exact ElasticitySchwartzCarleman.d_comm (e j) (e i) φ

open ElasticityAugmented TrivSqZeroExt

lemma de_fst (i : Fin 3) (v : Ext) : (de i v).fst = dc i v.fst := rfl
lemma de_snd (i : Fin 3) (v : Ext) : (de i v).snd = dd i v.snd := rfl
lemma de_inl (i : Fin 3) (a : Coeff) : de i (inl a) = inl (dc i a) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_inr (i : Fin 3) (u : Dist) : de i (inr u) = inr (dd i u) := by
  apply TrivSqZeroExt.ext <;> simp [de_fst,de_snd]
lemma de_commute (i j : Fin 3) (v : Ext) : de i (de j v) = de j (de i v) := by
  apply TrivSqZeroExt.ext
  · exact dc_commute i j v.fst
  · exact dd_commute i j v.snd

lemma sd_apply (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) : sd z i u = dd i u+z i • u := rfl
lemma shifted_inr (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) :
    shifted (A := Ext) de z i (inr u) = inr (sd z i u) := by
  simp only [shifted_apply,sd_apply,de_inr,inr_add,inr_smul]

lemma lapT_inr (z : Fin 3 → ℂ) (u : Dist) :
    lapT (shifted (A := Ext) de z) (inr u) = inr (lapd z u) := by
  simp only [lapT,lapd,shifted_inr,inr_sum]
lemma divT_inr (z : Fin 3 → ℂ) (u : Fin 3 → Dist) :
    divT (shifted (A := Ext) de z) (fun i => inr (u i)) = inr (divd z u) := by
  simp only [divT,divd,shifted_inr,inr_sum]
lemma LT_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) :
    LT (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) i = inr (phys z lam m u i) := by
  simp only [ElasticityAugmented.LT,phys,divT_inr,shifted_inr,inl_mul_inr,← inr_add,← inr_sum]
lemma RT_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 3) :
    RT de (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) (inr d) i =
      inr (rd z lam m u d i) := by
  simp only [RT,cmT,rd,lapT_inr,shifted_inr,de_inl,← inl_add,inl_mul_inr,← inr_add,← inr_sum]
lemma ST_inr (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (d : Dist) :
    ST de (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) (inr d) =
      inr (scd z lam m u d) := by
  simp only [ElasticityAugmented.ST,scd,lap,lapT_inr,shifted_inr,de_inl,← inl_add,inl_mul_inr,
    ← inl_sum,← inr_sum]
  simp only [two_mul,← inr_add]
  congr 1
  ext φ
  simp only [add_apply]
  change _ = _ + (2 : ℂ) * ((∑ i, dc i (lam+m) • sd z i d) φ) +
    (2 : ℂ) * ((∑ i, dc i m • lapd z (u i)) φ) +
    (2 : ℂ) * ((∑ i, ∑ j, dc i (dc j m) • sd z i (u j)) φ) + _
  ring

/-- The genuine distributional physical equation has the same compatible
augmented scalar-principal system as the smooth equation. No regularity of the
unknown is used in this differential identity. -/
theorem physical_expansion (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (i : Fin 3) :
    phys z lam m u i = rd z lam m u (divd z u) i := by
  have h := shifted_physical_expansion de z (inl lam) (inl m) (fun j => inr (u j)) de_commute i
  rw [LT_inr,divT_inr,RT_inr] at h
  exact congrArg TrivSqZeroExt.snd h

theorem physical_divergence (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) :
    divd z (phys z lam m u) = scd z lam m u (divd z u) := by
  have h := shifted_physical_divergence de z (inl lam) (inl m) (fun j => inr (u j)) de_commute
  have hL : ElasticityAugmented.LT (shifted (A := Ext) de z) (inl lam) (inl m) (fun j => inr (u j)) =
      (fun i => inr (phys z lam m u i)) := funext (LT_inr z lam m u)
  rw [hL,divT_inr,divT_inr,ST_inr] at h
  exact congrArg TrivSqZeroExt.snd h

lemma inl_two : inl (2 : Coeff) = (2 : Ext) := by
  exact inl_natCast 2
lemma coff_inl_mul (a b : Coeff) : (inl a : Ext)*inl b = inl (a*b) :=
  (inl_mul Dist a b).symm
lemma coff_inl_add (a b : Coeff) : (inl a : Ext)+inl b = inl (a+b) :=
  (inl_add Dist a b).symm
lemma coff_inl_sub (a b : Coeff) : (inl a : Ext)-inl b = inl (a-b) :=
  (inl_sub Dist a b).symm
lemma dist_inr_sub (u v : Dist) : (inr u : Ext)-inr v = inr (u-v) :=
  (inr_sub Coeff u v).symm
lemma coeff_two_smul (u : Dist) : (2 : Coeff) • u = (2 : ℂ) • u := by
  change TemperedDistribution.smulLeftCLM ℂ (fun _ : X => (2 : ℂ)) u = _
  rw [TemperedDistribution.smulLeftCLM_const]

lemma coeffA_inl (lam m n o : Coeff) (k : Fin 3) (i j : Fin 4) :
    coeffA (A := Ext) de (inl lam) (inl m) (inl n) (inl o) k i j = inl (coeffA dc lam m n o k i j) := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffA,Fin.cons_zero,Fin.cons_succ,coff_inl_add,de_inl,coff_inl_mul,
      coff_inl_sub,← inl_two]
  · split_ifs <;> rfl
  · split_ifs <;> simp only [coff_inl_add,add_zero,zero_add,inl_zero]
lemma coeffV_inl (lam m n o : Coeff) (i j : Fin 4) :
    coeffV (A := Ext) de (inl lam) (inl m) (inl n) (inl o) i j = inl (coeffV dc lam m n o i j) := by
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [coeffV,lap,Fin.cons_zero,Fin.cons_succ,de_inl,coff_inl_mul,← inl_sum,
      coff_inl_sub,← inl_two,inl_zero]
lemma normalizedPair_inr (z : Fin 3 → ℂ) (lam m n o : Coeff) (u : Fin 3 → Dist) (d : Dist) (i : Fin 4) :
    normalizedPair de (shifted (A := Ext) de z) (inl lam) (inl m) (inl n) (inl o) (fun j => inr (u j)) (inr d) i =
      inr (normPair z lam m n o u d i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [normalizedPair,normPair,Fin.cons_zero,ST_inr,RT_inr,de_inl,inl_mul_inr,
      ← inr_sum]
    rw [← inl_two,coff_inl_mul,inl_mul_inr,dist_inr_sub,inl_mul_inr]
    congr 1
    congr 1
    congr 1
    exact (mul_smul (2 : Coeff) n (∑ i, dc i m • rd z lam m u d i)).trans (coeff_two_smul _)
  · simp only [normalizedPair,normPair,Fin.cons_succ,RT_inr,inl_mul_inr]

/-- Genuine scalar-principal matrix form for the actual distribution system. -/
theorem normalized_matrix (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U : Fin 4 → Dist) (i : Fin 4) :
    normPair z lam m n o (fun j => U j.succ) (U 0) i =
      lapd z (U i)+(∑ k, ∑ j, coeffA dc lam m n o k i j • sd z k (U j))+
        (∑ j, coeffV dc lam m n o i j • U j) := by
  have hn' : (inl n : Ext)*inl m=1 := by rw [coff_inl_mul,hn]; rfl
  have ho' : (inl o : Ext)*(inl lam+inl m+inl m)=1 := by
    rw [coff_inl_add,coff_inl_add,coff_inl_mul,ho]; rfl
  have h := normalizedPair_matrix de (shifted (A := Ext) de z) (inl lam) (inl m) (inl n) (inl o)
    hn' ho' (fun j => inr (U j)) i
  simp only [normalizedPair_inr,lapT_inr,coeffA_inl,coeffV_inl,shifted_inr,inl_mul_inr,
    ← inr_sum,← inr_add] at h
  exact congrArg TrivSqZeroExt.snd h
end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma sobolev_sum {ι : Type*} (S : Finset ι) {s : ℝ} {v : ι → 𝓢'(E,F)}
    (hv : ∀ i ∈ S, MemSobolev s 2 (v i)) : MemSobolev s 2 (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi]
    exact (hv i (Finset.mem_insert_self _ _)).add
      (hS (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

lemma decay_memLp {s : ℝ} (hs : Module.finrank ℝ E < 2*s) :
    MemLp (fun x : E => (1+‖x‖^2)^(-s/2)) 2 := by
  have growth : (fun x : E => (1+‖x‖^2)^(-s/2)).HasTemperateGrowth := by fun_prop
  refine ⟨growth.1.continuous.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num)]
  suffices h : ∫⁻ x : E, ENNReal.ofReal ‖(1+‖x‖^2)^(-s)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    simp
  apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_decay_bound (x : E) (n k : ℕ) :
    ‖x‖^n*(1+‖x‖^2)^(-(n+k : ℝ)) ≤ (1+‖x‖^2)^(-(k : ℝ)) := by
  have hpos : 0 < 1+‖x‖^2 := by positivity
  have hbase : ‖x‖ ≤ 1+‖x‖^2 := by nlinarith [sq_nonneg (‖x‖-1)]
  calc
    _ ≤ (1+‖x‖^2)^n*(1+‖x‖^2)^(-(n+k : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbase n) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_add hpos]
      congr 1
      ring

lemma all_orders_fourier_moments {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ v : Lp F 1 (volume : Measure E), 𝓕 u = (v : 𝓢'(E,F)) ∧
      ∀ n : ℕ, Integrable (fun x => ‖x‖^n*‖v x‖) := by
  let k : ℕ := Module.finrank ℝ E+1
  have hk : (Module.finrank ℝ E : ℝ) < 2*k := by dsimp [k]; push_cast; linarith
  obtain ⟨v,hv⟩ := (hu k).fourier_memL1 hk
  refine ⟨v,hv,fun n => ?_⟩
  obtain ⟨w,hw⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp (hu (2*(n+k)))
  have hdec (m : ℕ) (hm : k ≤ m) : MemLp (fun x : E => (1+‖x‖^2)^(-(m : ℝ))) 2 := by
    have hh : (Module.finrank ℝ E : ℝ) < 2*(2*m) := by
      have : (k : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    convert decay_memLp hh using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    congr 1
    ring
  have hg : MemLp (fun x : E => Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ)))) 2 :=
    (hdec (n+k) (Nat.le_add_left _ _)).ofReal
  let q : Lp F 1 (volume : Measure E) := hg.toLp _ • w
  have hq : (q : 𝓢'(E,F)) = 𝓕 u := by
    rw [Lp.toTemperedDistribution_smul_eq (by fun_prop),← hw,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const (1 : ℂ) (𝓕 u)) using 1
    · congr 2
      ext x
      change Complex.ofReal ((1+‖x‖^2)^((↑(2*(n+k)) : ℝ)/2)) *
        Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) = 1
      rw [← Complex.ofReal_mul,← Complex.ofReal_one,Complex.ofReal_inj]
      rw [← Real.rpow_add (by positivity : 0 < (1+‖x‖^2 : ℝ))]
      convert Real.rpow_zero (1+‖x‖^2) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      push_cast
      ring
    · simp
  have heq : q=v := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := F))
    change (q : 𝓢'(E,F)) = (v : 𝓢'(E,F))
    rw [hq,hv]
  have hqa : ∀ᵐ x, v x = Complex.ofReal ((1+‖x‖^2)^(-(↑(n+k) : ℝ))) • w x := by
    rw [← heq]
    filter_upwards [Lp.coeFn_lpSMul (r := 1) (hg.toLp _) w, hg.coeFn_toLp] with x hx hy
    change q x = _ at hx
    rw [hx]
    change (hg.toLp _ : E → ℂ) x • w x = _
    rw [hy]
  have hi : Integrable (fun x : E => (1+‖x‖^2)^(-(k : ℝ))*‖w x‖) :=
    (hdec k le_rfl).integrable_mul (Lp.memLp w).norm
  apply hi.mono' ((continuous_norm.pow n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [hqa] with x hx
  change ‖‖x‖^n*‖v x‖‖ ≤ _
  rw [hx,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),← mul_assoc]
  simpa only [Nat.cast_add] using
    mul_le_mul_of_nonneg_right (weighted_decay_bound x n k) (norm_nonneg (w x))

end

section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma l1_inverse_fourier_distribution (v : Lp F 1 (volume : Measure E)) :
    (((Real.Lp.fourierTransformInv v).memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) =
      𝓕⁻ (v : 𝓢'(E,F)) := by
  ext φ
  rw [TemperedDistribution.fourierInv_apply,Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x : E, φ x • 𝓕⁻ (v : E → F) x := by
      apply integral_congr_ae
      filter_upwards [(Real.Lp.fourierTransformInv v).memLp_top.coeFn_toLp] with x hx
      rw [hx,Real.Lp.fourierTransformInv_apply]
    _ = ∫ x : E, (𝓕⁻ φ) x • v x := by
      have hf : (-innerₗ E).flip = -innerₗ E := by
        ext x y
        exact congrArg Neg.neg (real_inner_comm x y)
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
        (L := -innerₗ E) (μ := (volume : Measure E)) (ν := volume) Real.continuous_fourierChar
        (show Continuous (fun p : E × E => -inner ℝ p.1 p.2) by fun_prop) φ.integrable (L1.integrable_coeFn v)
      rw [hf] at h
      simp only [SchwartzMap.fourierInv_coe]
      convert h.symm using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := rfl
  rfl

/-- A tempered distribution lying in all integral Sobolev spaces has an actual
bounded smooth representative. All moments of a single L1 Fourier representative
are proved first, so the smooth representatives do not depend on the order. -/
theorem all_orders_smooth_representative {u : 𝓢'(E,F)}
    (hu : ∀ n : ℕ, MemSobolev n 2 u) :
    ∃ g : BoundedContinuousFunction E F, ContDiff ℝ (⊤ : ℕ∞) (g : E → F) ∧
      u = ((g.memLp_top.toLp _ : Lp F ∞ (volume : Measure E)) : 𝓢'(E,F)) := by
  obtain ⟨v,hv,hm⟩ := all_orders_fourier_moments hu
  refine ⟨Real.Lp.fourierTransformInv v,?_,?_⟩
  · have hs := Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => hm n)
    convert hs.comp contDiff_neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact (Real.Lp.fourierTransformInv_apply v x).trans (Real.fourierInv_eq_fourier_neg _ _)
  · rw [l1_inverse_fourier_distribution,← hv,fourierInv_fourier_eq]

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

lemma LocalSobolev.mono {Ω : Set E} {s t : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) (hst : t ≤ s) : LocalSobolev Ω t u :=
  fun g hg hc hs => (h g hg hc hs).mono hst

lemma LocalSobolev.product_derivative {Ω : Set E} {s : ℝ} {u : 𝓢'(E,F)}
    (h : LocalSobolev Ω s u) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) (m : E) :
    MemSobolev (s-1) 2 (smulLeftCLM F g (∂_{m} u)) := by
  have hdg := (compact_derivative hc m).hasTemperateGrowth (smooth_derivative hg m)
  have h1 := (h g hg hc hs).lineDerivOp (m := m)
  have h2 := h _ (smooth_derivative hg m) (compact_derivative hc m)
    ((derivative_support_subset g m).trans hs)
  have h3 := h1.sub (h2.mono (by linarith : s-1 ≤ s))
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) m hdg,add_sub_cancel_left] at h3
  exact h3

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma laplacian_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,F)) :
    Δ (smulLeftCLM F g u) = smulLeftCLM F g (Δ u)+
      ∑ d, (smulLeftCLM F (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b d)) x (b d)) u+
        (2 : ℂ) • smulLeftCLM F (fun x => fderiv ℝ g x (b d)) (∂_{b d} u)) := by
  classical
  rw [laplacian_eq_sum b,laplacian_eq_sum b,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hgd := smooth_derivative hg (b d)
  have hcd := compact_derivative hc (b d)
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),LineDeriv.lineDerivOp_add,
    distribution_leibniz (hcd.hasTemperateGrowth hgd) _
      ((compact_derivative hcd (b d)).hasTemperateGrowth (smooth_derivative hgd (b d))),
    distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd)]
  module

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
namespace LocalEq
variable {Ω : Set X} {u v w u' v' : Dist}
lemma add (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u+u') (v+v') := by
  intro φ hc hs
  simp only [add_apply,h φ hc hs,h' φ hc hs]
lemma sub (h : LocalEq Ω u v) (h' : LocalEq Ω u' v') : LocalEq Ω (u-u') (v-v') := by
  intro φ hc hs
  simp only [sub_apply,h φ hc hs,h' φ hc hs]
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
lemma sum {ι : Type*} (s : Finset ι) {a b : ι → Dist} (h : ∀ i ∈ s, LocalEq Ω (a i) (b i)) :
    LocalEq Ω (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  intro φ hc hs
  simp only [sum_apply]
  exact Finset.sum_congr rfl (fun i hi => h i hi φ hc hs)
lemma coeff (h : LocalEq Ω u v) (a : Coeff) : LocalEq Ω (a • u) (a • v) := by
  intro φ hc hs
  change u (SchwartzMap.smulLeftCLM ℂ (eval a) φ) = v (SchwartzMap.smulLeftCLM ℂ (eval a) φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (growth a),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_left : HasCompactSupport (eval a * (φ : X → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (growth a),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_right (f := eval a) (g := (φ : X → ℂ))).trans hs
lemma derivative (h : LocalEq Ω u v) (i : Fin 3) : LocalEq Ω (dd i u) (dd i v) := by
  intro φ hc hs
  change u (- ∂_{e i} φ) = v (- ∂_{e i} φ)
  apply h
  · change HasCompactSupport (fun x => -((∂_{e i} φ : Test) x))
    exact (hc.fderiv_apply (𝕜 := ℝ) (e i)).neg
  · change tsupport (-((∂_{e i} φ : Test) : X → ℂ)) ⊆ Ω
    rw [tsupport_neg]
    exact (ElasticityRegularity.derivative_support_subset (φ : X → ℂ) (e i)).trans hs
lemma cutoff (h : LocalEq Ω u v) {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : X → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : X → ℂ))).trans hs
end LocalEq

lemma LocalEq.shifted {Ω : Set X} {u v : Dist} (h : LocalEq Ω u v) (z : Fin 3 → ℂ) (i : Fin 3) :
    LocalEq Ω (sd z i u) (sd z i v) :=
  (h.derivative i).add (h.smul (z i))
lemma LocalEq.divergence {Ω : Set X} {u v : Fin 3 → Dist} (h : ∀ i, LocalEq Ω (u i) (v i))
    (z : Fin 3 → ℂ) : LocalEq Ω (divd z u) (divd z v) :=
  LocalEq.sum Finset.univ (fun i _ => (h i).shifted z i)

/-- The local physical stress-divergence equation implies the true normalized
augmented equation. The fourth component is the actual shifted divergence. -/
theorem local_normalized_system {Ω : Set X} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (u F : Fin 3 → Dist) (h : ∀ i, LocalEq Ω (phys z lam m u i) (F i)) :
    ∀ i, LocalEq Ω (normPair z lam m n o u (divd z u) i) (normSource z m n o F i) := by
  have hr (i : Fin 3) : LocalEq Ω (rd z lam m u (divd z u) i) (F i) := by
    rw [← physical_expansion]
    exact h i
  have hs : LocalEq Ω (scd z lam m u (divd z u)) (divd z F) := by
    rw [← physical_divergence]
    exact LocalEq.divergence h z
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact (hs.sub (((LocalEq.sum Finset.univ (fun j _ => (hr j).coeff (dc j m))).coeff n).smul 2)).coeff o
  · exact (hr i).coeff n

lemma lapd_expand (z : Fin 3 → ℂ) (u : Dist) :
    lapd z u = Δ u + (∑ i, (2*z i) • dd i u)+(∑ i, z i*z i) • u := by
  have he (i : Fin 3) : sd z i (sd z i u)=dd i (dd i u)+(2*z i) • dd i u+(z i*z i) • u := by
    simp only [sd_apply,map_add,map_smul,smul_add,smul_smul]
    module
  rw [lapd]
  simp only [he,Finset.sum_add_distrib,← Finset.sum_smul]
  congr 2
  simpa only [dd_apply,e,EuclideanSpace.basisFun_apply] using
    (laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ) u).symm

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma MemSobolev.local_zero {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) (Ω : Set E) :
    LocalSobolev Ω 0 u := by
  intro g hg hc _
  exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity
namespace LocalSobolev
variable {Ω : Set X} {s t : ℝ} {u v : Dist}
lemma add (h : ElasticityRegularity.LocalSobolev Ω s u)
    (h' : ElasticityRegularity.LocalSobolev Ω s v) :
    ElasticityRegularity.LocalSobolev Ω s (u+v) := by
  intro g hg hc hs
  rw [map_add]
  exact (h g hg hc hs).add (h' g hg hc hs)
lemma sub (h : ElasticityRegularity.LocalSobolev Ω s u)
    (h' : ElasticityRegularity.LocalSobolev Ω s v) :
    ElasticityRegularity.LocalSobolev Ω s (u-v) := by
  intro g hg hc hs
  rw [map_sub]
  exact (h g hg hc hs).sub (h' g hg hc hs)
lemma smul (h : ElasticityRegularity.LocalSobolev Ω s u) (c : ℂ) :
    ElasticityRegularity.LocalSobolev Ω s (c • u) := by
  intro g hg hc hs
  rw [map_smul]
  exact (h g hg hc hs).smul c
lemma sum {ι : Type*} (S : Finset ι) {u : ι → Dist}
    (h : ∀ i ∈ S, ElasticityRegularity.LocalSobolev Ω s (u i)) :
    ElasticityRegularity.LocalSobolev Ω s (∑ i ∈ S, u i) := by
  intro g hg hc hs
  rw [map_sum]
  exact sobolev_sum S (fun i hi => h i hi g hg hc hs)
lemma coeff (h : ElasticityRegularity.LocalSobolev Ω s u) (a : Coeff) :
    ElasticityRegularity.LocalSobolev Ω s (a • u) := by
  intro g hg hc hs
  have := h (g*eval a) (hg.mul (eval_smooth a)) hc.mul_right (tsupport_mul_subset_left.trans hs)
  change MemSobolev s 2 (smulLeftCLM ℂ g (smulLeftCLM ℂ (eval a) u))
  rw [smulLeftCLM_smulLeftCLM_apply (growth a) (hc.hasTemperateGrowth hg),mul_comm]
  exact this
lemma derivative (h : ElasticityRegularity.LocalSobolev Ω s u) (i : Fin 3) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (dd i u) := by
  intro g hg hc hs
  exact h.product_derivative hg hc hs (e i)
lemma shifted (h : ElasticityRegularity.LocalSobolev Ω s u) (z : Fin 3 → ℂ) (i : Fin 3) :
    ElasticityRegularity.LocalSobolev Ω (s-1) (sd z i u) :=
  add (derivative h i) (smul (h.mono (by linarith)) (z i))
lemma divergence {u : Fin 3 → Dist} (h : ∀ i, ElasticityRegularity.LocalSobolev Ω s (u i))
    (z : Fin 3 → ℂ) : ElasticityRegularity.LocalSobolev Ω (s-1) (divd z u) :=
  sum Finset.univ (fun i _ => shifted (h i) z i)
end LocalSobolev

lemma LocalEq.localSobolev {Ω : Set X} {s : ℝ} {u v : Dist} (h : LocalEq Ω u v)
    (hv : ElasticityRegularity.LocalSobolev Ω s v) : ElasticityRegularity.LocalSobolev Ω s u := by
  intro g hg hc hs
  rw [h.cutoff hg hc hs]
  exact hv g hg hc hs

/-- Local gain from an actual distributional Laplacian; includes negative order
starting points. The cutoff commutator is proved, not silently discarded. -/
theorem local_laplacian_gain {Ω : Set X} {s : ℝ} {u : Dist}
    (hu : ElasticityRegularity.LocalSobolev Ω s u)
    (hΔ : ElasticityRegularity.LocalSobolev Ω (s-1) (Δ u)) :
    ElasticityRegularity.LocalSobolev Ω (s+1) u := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  intro g hg hgc hgs
  have hb : MemSobolev (s-1) 2 (Δ (smulLeftCLM ℂ g u)) := by
    rw [laplacian_product b hg hgc]
    apply (hΔ g hg hgc hgs).add
    apply sobolev_sum Finset.univ
    intro d _
    have hgd := smooth_derivative hg (b d)
    have hcd := compact_derivative hgc (b d)
    have hsd := (derivative_support_subset g (b d)).trans hgs
    exact ((hu _ (smooth_derivative hgd (b d)) (compact_derivative hcd (b d))
      ((derivative_support_subset _ (b d)).trans hsd)).mono (by linarith)).add
        ((hu.product_derivative hgd hcd hsd (b d)).smul 2)
  have h := laplacian_gain ((hu g hg hgc hgs).mono (by linarith : s-1 ≤ s)) hb
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma normSource_local {Ω : Set X} {s : ℝ} (z : Fin 3 → ℂ) (m n o : Coeff)
    (F : Fin 3 → Dist) (hF : ∀ i, ElasticityRegularity.LocalSobolev Ω s (F i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s-1) (normSource z m n o F i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact LocalSobolev.coeff (LocalSobolev.sub (LocalSobolev.divergence hF z)
      (LocalSobolev.smul (LocalSobolev.coeff (LocalSobolev.sum Finset.univ (fun i _ =>
        LocalSobolev.coeff ((hF i).mono (by linarith)) (dc i m))) n) 2)) o
  · exact LocalSobolev.coeff ((hF i).mono (by linarith)) n

/-- Interior elliptic gain for the genuine normalized physical distribution
system, with no solution-regularity premise hidden in the equation. -/
theorem normalized_local_gain {Ω : Set X} {s : ℝ} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (U F : Fin 4 → Dist)
    (heq : ∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (F i))
    (hU : ∀ i, ElasticityRegularity.LocalSobolev Ω s (U i))
    (hF : ∀ i, ElasticityRegularity.LocalSobolev Ω (s-1) (F i)) :
    ∀ i, ElasticityRegularity.LocalSobolev Ω (s+1) (U i) := by
  intro i
  let l₁ : Dist := ∑ k, ∑ j, coeffA (A := Coeff) dc lam m n o k i j • sd z k (U j)
  let l₀ : Dist := ∑ j, coeffV (A := Coeff) dc lam m n o i j • U j
  have h₁ : ElasticityRegularity.LocalSobolev Ω (s-1) l₁ := by
    apply LocalSobolev.sum
    intro k _
    apply LocalSobolev.sum
    intro j _
    exact LocalSobolev.coeff (LocalSobolev.shifted (hU j) z k) _
  have h₀ : ElasticityRegularity.LocalSobolev Ω (s-1) l₀ := by
    apply LocalSobolev.sum
    intro j _
    exact LocalSobolev.coeff ((hU j).mono (by linarith)) _
  have he : LocalEq Ω (lapd z (U i)) (F i-l₁-l₀) := by
    intro φ hc hs
    have hh := heq i φ hc hs
    rw [normalized_matrix z lam m n o hn ho] at hh
    change ((lapd z (U i)+l₁+l₀) : Dist) φ=(F i) φ at hh
    simp only [add_apply,sub_apply] at hh ⊢
    linear_combination hh
  have hlap := he.localSobolev (LocalSobolev.sub (LocalSobolev.sub (hF i) h₁) h₀)
  have hd : ElasticityRegularity.LocalSobolev Ω (s-1) (∑ k, (2*z k) • dd k (U i)) :=
    LocalSobolev.sum Finset.univ (fun k _ => LocalSobolev.smul
      (LocalSobolev.derivative (hU i) k) (2*z k))
  have hz : ElasticityRegularity.LocalSobolev Ω (s-1) ((∑ k, z k*z k) • U i) :=
    LocalSobolev.smul ((hU i).mono (by linarith)) _
  apply local_laplacian_gain (hU i)
  have hΔ := LocalSobolev.sub (LocalSobolev.sub hlap hz) hd
  simpa only [lapd_expand,add_sub_cancel_right] using hΔ

/-- All local Sobolev orders for an L2 physical solution with smooth source.
The physical fourth unknown is the actual shifted divergence, initially H^-1,
not an independent L2 unknown postulated as a hypothesis. -/
theorem physical_local_all_orders {Ω : Set X} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (u F : Fin 3 → Dist)
    (heq : ∀ i, LocalEq Ω (phys z lam m u i) (F i))
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (F i)) :
    ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N ((Fin.cons (divd z u) u : Fin 4 → Dist) i) := by
  let U : Fin 4 → Dist := Fin.cons (divd z u) u
  let FF := normSource z m n o F
  have hsys : ∀ i, LocalEq Ω (normPair z lam m n o (fun j => U j.succ) (U 0) i) (FF i) :=
    local_normalized_system z lam m n o u F heq
  have hm : ∀ i, ElasticityRegularity.LocalSobolev Ω (-1) (U i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change ElasticityRegularity.LocalSobolev Ω (-1) (divd z u)
      simpa only [zero_sub] using LocalSobolev.divergence hu z
    · exact (hu i).mono (by norm_num)
  have hzero : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (U i) := by
    have hh := normalized_local_gain (s := -1) z lam m n o hn ho U FF hsys hm
      (fun i => (normSource_local z m n o F (hf 0) i).mono (by norm_num))
    simpa only [neg_add_cancel] using hh
  intro N
  induction N with
  | zero => rw [Nat.cast_zero]; exact hzero
  | succ N hN =>
    rw [Nat.cast_add,Nat.cast_one]
    exact normalized_local_gain z lam m n o hn ho U FF hsys hN
      (normSource_local z m n o F (hf N))

/-- Every compact cutoff of the actual augmented physical unknown has a single
bounded smooth representative. This is a conclusion, not an assumed classical
regularity theorem. -/
theorem physical_cutoff_smooth {Ω : Set X} (z : Fin 3 → ℂ) (lam m n o : Coeff)
    (hn : n*m=1) (ho : o*(lam+m+m)=1) (u F : Fin 3 → Dist)
    (heq : ∀ i, LocalEq Ω (phys z lam m u i) (F i))
    (hu : ∀ i, ElasticityRegularity.LocalSobolev Ω 0 (u i))
    (hf : ∀ N : ℕ, ∀ i, ElasticityRegularity.LocalSobolev Ω N (F i))
    (i : Fin 4) {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    ∃ v : BoundedContinuousFunction X ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : X → ℂ) ∧
      smulLeftCLM ℂ g ((Fin.cons (divd z u) u : Fin 4 → Dist) i) =
        ((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure X)) : Dist) := by
  exact all_orders_smooth_representative (fun N =>
    physical_local_all_orders z lam m n o hn ho u F heq hu hf N i g hg hgc hgs)
end ElasticityDistribution

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
namespace ElasticityDualSolvability

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A lower norm estimate on an (unbounded) test operator gives a weak solution
for every Hilbert-space forcing, with precisely the same constant. No density
or completeness of the test space, or closedness of the range, is assumed. -/
theorem exists_weak_solution (D : Submodule ℂ H) (A : D →ₗ[ℂ] H)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ v : D, ‖(v : H)‖ ≤ C * ‖A v‖) (f : H) :
    ∃ z : H, ‖z‖ ≤ C * ‖f‖ ∧ ∀ v : D, inner ℂ z (A v) = inner ℂ f (v : H) := by
  have hinj : Function.Injective A := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply Subtype.val_injective
    apply norm_eq_zero.mp
    have ht := hA (v-w)
    rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at ht
    exact le_antisymm ht (norm_nonneg _)
  let T := (LinearEquiv.ofInjective A hinj).symm
  let l : A.range →ₗ[ℂ] ℂ :=
    ((innerSL ℂ f).toLinearMap.comp D.subtype).comp T.toLinearMap
  have hT (y : A.range) : A (T y) = (y : H) := by
    exact congrArg Subtype.val ((LinearEquiv.ofInjective A hinj).apply_symm_apply y)
  have hl : ∀ y : A.range, ‖l y‖ ≤ (C*‖f‖)*‖y‖ := by
    intro y
    change ‖inner ℂ f ((T y : D) : H)‖ ≤ _
    calc
      _ ≤ ‖f‖ * ‖((T y : D) : H)‖ := norm_inner_le_norm _ _
      _ ≤ ‖f‖ * (C*‖A (T y)‖) := mul_le_mul_of_nonneg_left (hA (T y)) (norm_nonneg _)
      _ = _ := by rw [hT]; change ‖f‖ * (C * ‖y‖) = _; ring
  let L : A.range →L[ℂ] ℂ := l.mkContinuous (C*‖f‖) hl
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq A.range L
  let z : H := (InnerProductSpace.toDual ℂ H).symm G
  refine ⟨z, ?_, fun v => ?_⟩
  · calc
      ‖z‖ = ‖G‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
      _ = ‖L‖ := hnorm
      _ ≤ C*‖f‖ := l.mkContinuous_norm_le (mul_nonneg hC (norm_nonneg _)) hl
  · change inner ℂ ((InnerProductSpace.toDual ℂ H).symm G) (A v) = _
    rw [InnerProductSpace.toDual_symm_apply]
    change G ((LinearEquiv.ofInjective A hinj v : A.range) : H) = _
    rw [hG]
    change inner ℂ f ((T (LinearEquiv.ofInjective A hinj v) : D) : H) = _
    rw [LinearEquiv.symm_apply_apply]

end ElasticityDualSolvability

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalDual
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra ElasticityPhysicalEstimate

lemma embed_apply (u : Fin 3 → S) (i : Fin 3) : embed u i = L2 (u i) := rfl

lemma embed_injective : Function.Injective embed := by
  intro u v h
  funext i
  apply SchwartzMap.injective_toLp 2 volume
  exact congrArg (fun w : H => w i) h

lemma norm_embed (h : ℝ) (u : Fin 3 → S) : ‖embed u‖ = sobNorm h 0 u := by
  rw [PiLp.norm_eq_of_L2]
  simp only [embed_apply, sobNorm, J_zero, norm2]

/-- The physical weak equation follows from the actual uniform test estimate.
The forcing and unknown belong to the genuine vector-valued L2 Hilbert space. -/
theorem weak_physical_from_test (R h : ℝ) (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (htest : ∀ u : Fin 3 → S, (∀ i, BallSupported R (u i)) →
      sobNorm h 0 u ≤ C*sobNorm h 0 (physical (adjPhase z) lam m u)) (F : H) :
    ∃ w : H, ‖w‖ ≤ C*‖F‖ ∧ ∀ v : Fin 3 → S, (∀ i, BallSupported R (v i)) →
      inner ℂ w (embed (physical (adjPhase z) lam m v)) = inner ℂ F (embed v) := by
  let V := supported R
  let T : V →ₗ[ℂ] H := embed.comp V.subtype
  have hinj : Function.Injective T := by
    intro v w hvw
    exact Subtype.val_injective (embed_injective hvw)
  let E := LinearEquiv.ofInjective T hinj
  let B : T.range →ₗ[ℂ] H :=
    (((embed.comp (physicalLM (adjPhase z) lam m)).comp V.subtype).comp E.symm.toLinearMap)
  have hT (y : T.range) : T (E.symm y) = (y : H) :=
    congrArg Subtype.val (E.apply_symm_apply y)
  have hB (y : T.range) : ‖(y : H)‖ ≤ C*‖B y‖ := by
    rw [← hT y]
    change ‖embed ((E.symm y : V) : Fin 3 → S)‖ ≤
      C * ‖embed (physical (adjPhase z) lam m ((E.symm y : V) : Fin 3 → S))‖
    rw [norm_embed h, norm_embed h]
    exact htest _ (E.symm y).property
  obtain ⟨w, hw, heq⟩ := ElasticityDualSolvability.exists_weak_solution T.range B C hC hB F
  refine ⟨w, hw, fun v hv => ?_⟩
  let v' : V := ⟨v, hv⟩
  have hh := heq (E v')
  change inner ℂ w (embed (physical (adjPhase z) lam m ((E.symm (E v') : V) : Fin 3 → S))) =
    inner ℂ F (T v') at hh
  rw [E.symm_apply_apply] at hh
  exact hh

lemma adjPhase_phase (h : ℝ) (α β : X) :
    adjPhase (phase h α β) = phase h (-α) β := by
  funext i
  simp only [adjPhase, phase, Complex.star_def, map_div₀, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I, PiLp.neg_apply, Complex.ofReal_neg]
  ring

end ElasticityPhysicalDual

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
namespace ElasticityDistribution

section

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder
lemma cj_add (φ ψ : S) : cj (φ+ψ) = cj φ+cj ψ := by ext x; simp
lemma cj_smul (c : ℂ) (φ : S) : cj (c • φ) = star c • cj φ := by ext x; simp
lemma cj_sum {ι : Type*} (s : Finset ι) (φ : ι → S) : cj (∑ i ∈ s, φ i) = ∑ i ∈ s, cj (φ i) := by
  ext x
  simp
lemma cj_deriv (i : Fin 3) (φ : S) : cj (∂_{ElasticityAugmented.e i} φ) = ∂_{ElasticityAugmented.e i} (cj φ) := by
  ext x
  change star (fderiv ℝ φ x (ElasticityAugmented.e i)) = fderiv ℝ (cj φ) x (ElasticityAugmented.e i)
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (φ.hasFDerivAt x)
  exact (congrArg (fun T : X →L[ℝ] ℂ => T (ElasticityAugmented.e i)) h.fderiv).symm
lemma cj_shift (z : Fin 3 → ℂ) (i : Fin 3) (φ : S) :
    cj (shiftD z i φ) = shiftD (fun i => star (z i)) i (cj φ) := by
  simp only [shiftD_apply,cj_add,cj_smul]
  congr 1
  exact cj_deriv i φ
lemma cj_mult (a : X → ℂ) (ha : a.HasTemperateGrowth) (hr : ∀ x, star (a x)=a x) (φ : S) :
    cj (mult a φ) = mult a (cj φ) := by
  ext x
  simp only [cj_apply,mult_apply a ha,star_mul,hr]
  exact mul_comm _ _
lemma cj_physical (z : Fin 3 → ℂ) (lam m : X → ℂ)
    (hl : lam.HasTemperateGrowth) (hm : m.HasTemperateGrowth)
    (hrl : ∀ x, star (lam x)=lam x) (hrm : ∀ x, star (m x)=m x) (φ : Fin 3 → S)
    {index : Fin 3} :
    cj (physical z lam m φ index) =
      physical (fun i => star (z i)) lam m (fun i => cj (φ i)) index := by
  simp only [physical,cj_add,cj_shift,cj_mult lam hl hrl,cj_mult m hm hrm,cj_sum]
lemma cj_supported {R : ℝ} {φ : S} (h : BallSupported R φ) : BallSupported R (cj φ) := by
  intro x hx
  exact h x (fun h0 => hx (by simp [h0]))
lemma Lp_test (w : Lp ℂ 2 (volume : Measure X)) (φ : S) :
    (w : Dist) φ = inner ℂ (ElasticityBessel.L2 (cj φ)) w := by
  rw [Lp.toTemperedDistribution_apply,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cj φ).coeFn_toLp 2 volume] with x hx
  change φ x • w x = inner ℂ ((ElasticityBessel.L2 (cj φ)) x) (w x)
  change (ElasticityBessel.L2 (cj φ) : X → ℂ) x = cj φ x at hx
  rw [hx]
  simp only [cj_apply,RCLike.inner_apply',starRingEnd_apply,star_star,smul_eq_mul,mul_comm]

open ElasticityAugmented TemperedDistribution
open ElasticityPhysicalAlgebra (shiftD shiftD_apply)
open ElasticityNegativeOrder (mult)

lemma sd_test (z : Fin 3 → ℂ) (i : Fin 3) (u : Dist) (φ : S) :
    (sd z i u) φ = -u (shiftD (-z) i φ) := by
  simp only [sd_apply,dd_apply,lineDerivOp_apply_apply,add_apply,smul_apply,
    shiftD_apply,map_neg,map_add,map_smul,Pi.neg_apply,neg_smul]
  change -u (∂_{e i} φ)+z i • u φ = -(u (∂_{e i} φ)+ -(z i • u φ))
  abel
lemma coeff_test (a : Coeff) (u : Dist) (φ : S) :
    (a • u) φ = u (mult (eval a) φ) := rfl
lemma coeff_smul_add (a : Coeff) (u v : Dist) : a • (u+v)=a•u+a•v :=
  (TemperedDistribution.smulLeftCLM ℂ (eval a)).map_add u v
lemma two_sd_test (z : Fin 3 → ℂ) (i j : Fin 3) (a : Coeff) (u : Dist) (φ : S) :
    (sd z i (a • sd z j u)) φ =
      u (shiftD (-z) j (mult (eval a) (shiftD (-z) i φ))) := by
  rw [sd_test,coeff_test,sd_test,neg_neg]

/-- Formal transpose of the actual complex physical distribution operator.
It is proved by evaluation on Schwartz tests, so no integration-by-parts
regularity of the unknown is assumed. -/
theorem physical_transpose (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → Dist) (φ : Fin 3 → S) :
    (∑ i, phys z lam m u i (φ i)) =
      ∑ i, u i (ElasticityPhysicalAlgebra.physical (-z) (eval lam) (eval m) φ i) := by
  have h_lam : (∑ i, ∑ j, u j (shiftD (-z) j (mult (eval lam) (shiftD (-z) i (φ i))))) =
      ∑ i, ∑ j, u i (shiftD (-z) i (mult (eval lam) (shiftD (-z) j (φ j)))) :=
    Finset.sum_comm
  have hm : (∑ i, ∑ j, u j (shiftD (-z) i (mult (eval m) (shiftD (-z) j (φ i))))) =
      ∑ i, ∑ j, u i (shiftD (-z) j (mult (eval m) (shiftD (-z) i (φ j)))) :=
    Finset.sum_comm
  simp only [phys,divd,Finset.smul_sum,map_sum,coeff_smul_add,map_add,sum_apply,add_apply,
    two_sd_test,Finset.sum_add_distrib,
    ElasticityPhysicalAlgebra.physical]
  rw [h_lam,hm]

end

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder

/-- The actual Hilbert weak equation is the actual physical distribution equation.
This lemma does not assume regularity of the unknown and does not replace the
physical stress-divergence operator by an abstract PDE hypothesis. -/
theorem weak_to_vector_distribution (R : ℝ) (z : Fin 3 → ℂ) (lam m : Coeff)
    (hrl : ∀ x, star (eval lam x)=eval lam x) (hrm : ∀ x, star (eval m x)=eval m x)
    (w F : _root_.OAI.ElasticityPhysicalDual.H)
    (heq : ∀ v : Fin 3 → S, (∀ i, BallSupported R (v i)) →
      inner ℂ w (embed (physical (adjPhase z) (eval lam) (eval m) v)) = inner ℂ F (embed v))
    (φ : Fin 3 → S) (hφ : ∀ i, BallSupported R (φ i)) :
    (∑ i, phys z lam m (fun j => (w j : Dist)) i (φ i)) =
      ∑ i, (F i : Dist) (φ i) := by
  rw [physical_transpose]
  simp only [Lp_test]
  have h := congrArg star (heq (fun i => cj (φ i)) (fun i => cj_supported (hφ i)))
  have hs (a b : _root_.OAI.ElasticityPhysicalDual.H) : star (inner ℂ a b)=inner ℂ b a :=
    inner_conj_symm (𝕜 := ℂ) b a
  simp only [hs] at h
  rw [PiLp.inner_apply,PiLp.inner_apply] at h
  have hh (i : Fin 3) : physical (adjPhase z) (eval lam) (eval m) (fun j => cj (φ j)) i =
      cj (physical (-z) (eval lam) (eval m) φ i) := by
    rw [cj_physical _ _ _ (growth lam) (growth m) hrl hrm]
    rfl
  simpa only [embed_apply,hh] using h

theorem weak_to_local_physical (Ω : Set X) (R : ℝ) (hΩ : Ω ⊆ Metric.closedBall 0 R)
    (z : Fin 3 → ℂ) (lam m : Coeff)
    (hrl : ∀ x, star (eval lam x)=eval lam x) (hrm : ∀ x, star (eval m x)=eval m x)
    (w F : _root_.OAI.ElasticityPhysicalDual.H)
    (heq : ∀ v : Fin 3 → S, (∀ i, BallSupported R (v i)) →
      inner ℂ w (embed (physical (adjPhase z) (eval lam) (eval m) v)) = inner ℂ F (embed v)) :
    ∀ i, LocalEq Ω (phys z lam m (fun j => (w j : Dist)) i) (F i : Dist) := by
  classical
  intro i φ _hc hs
  let ψ : Fin 3 → S := fun j => if j=i then φ else 0
  have hψ : ∀ j, BallSupported R (ψ j) := by
    intro j
    by_cases hji : j=i
    · intro x hx
      have hx' : φ x ≠ 0 := by simpa only [ψ,ite_eq_left hji] using hx
      have hxx := hΩ (hs (subset_tsupport _ hx'))
      simpa only [Metric.mem_closedBall,dist_zero_right] using hxx
    · simpa only [ψ,ite_eq_right hji] using BallSupported.zero R
  have h := weak_to_vector_distribution R z lam m hrl hrm w F heq ψ hψ
  simpa only [ψ,apply_ite,map_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h
end ElasticityDistribution

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

theorem physical_test_exterior (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ u : Fin 3 → S, (∀ i, BallSupported R (u i)) →
        sobNorm h 0 u ≤ C*sobNorm h 0 (physical (phase h α β) lam m u) := by
  let n := reciprocal m hm0
  let o := reciprocal (lam+m+m) he0
  have hn : ExteriorConstant n := hm.reciprocal hm0
  have ho : ExteriorConstant o := ((hl.add hm).add hm).reciprocal he0
  have ha := exterior_coeffA hl hm hn ho
  have hv := exterior_coeffV hl hm hn ho
  have hc := exterior_cPhys hm hn
  obtain ⟨M, hM, hbM⟩ := ExteriorConstant.uniform_bound
    (fun ij : Fin 3 × Fin 4 × Fin 4 => coeffA coord lam m n o ij.1 ij.2.1 ij.2.2)
    (fun ij => ha ij.1 ij.2.1 ij.2.2)
  obtain ⟨V, hV, hbV⟩ := ExteriorConstant.uniform_bound
    (fun ij : Fin 4 × Fin 4 => coeffV coord lam m n o ij.1 ij.2)
    (fun ij => hv ij.1 ij.2)
  obtain ⟨A₁, hA₁, hnA⟩ := hn.bound
  obtain ⟨A₂, hA₂, hoA⟩ := ho.bound
  obtain ⟨A₃, hA₃, hcA⟩ := ExteriorConstant.uniform_bound (fun i => -2*n*coord i m) hc
  obtain ⟨D, hD, hod⟩ := ExteriorConstant.uniform_bound (fun i => coord i o) (fun i => ho.coord i)
  let Z : ℝ := ∑ i, ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖
  have hZ : 0 ≤ Z := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hbZ (i : Fin 3) : ‖((α i : ℂ)+Complex.I*(β i : ℂ))‖ ≤ Z :=
    Finset.single_le_sum (fun j _ => norm_nonneg ((α j : ℂ)+Complex.I*(β j : ℂ))) (Finset.mem_univ i)
  apply physical_test_estimate R hR α β hα lam m n o (reciprocal_mul m hm0)
    (reciprocal_mul (lam+m+m) he0) hl.growth hm.growth hn.growth ho.growth
    (fun k i j => (ha k i j).growth) (fun i j => (hv i j).growth) (fun i => (hc i).growth)
    M V (A₁+A₂+A₃) D Z hM hV (by positivity) hD hZ
  · intro k i j x
    simpa only [aPhys, Pi.neg_apply, norm_neg] using hbM (k, i, j) x
  · intro i j x
    simpa only [vPhys, Pi.neg_apply, norm_neg] using hbV (i, j) x
  · intro x
    linarith [hnA x]
  · intro x
    linarith [hoA x]
  · intro i x
    have hh := hcA i x
    change ‖((-2*n*coord i m : Smooth) : X → ℂ) x‖ ≤ _
    linarith
  · exact fun x i => hod i x
  · exact hbZ

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalSolvability
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityAugmented
open ElasticityPhysicalAlgebra (physical phase)
open ElasticityPhysicalDual ElasticityCoeffBounds

theorem weak_solvability (R : ℝ) (hR : 1 ≤ R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ F : H, ∃ w : H, ‖w‖ ≤ C*‖F‖ ∧ ∀ v : Fin 3 → S,
        (∀ i, BallSupported R (v i)) →
        inner ℂ w (embed (physical (adjPhase (phase h α β)) lam m v)) =
          inner ℂ F (embed v) := by
  obtain ⟨C, h₀, hC, hh₀, hest⟩ := physical_test_exterior R hR (-α) β
    (neg_ne_zero.mpr hα) lam m hl hm hm0 he0
  refine ⟨C, h₀, hC, hh₀, fun h hh hsmall F => ?_⟩
  apply weak_physical_from_test R h (phase h α β) lam m C hC.le ?_ F
  intro u hu
  rw [adjPhase_phase]
  exact hest h hh hsmall u hu

end ElasticityPhysicalSolvability

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

lemma lp_local_zero (Ω : Set X) (u : Lp ℂ 2 (volume : Measure X)) :
    ElasticityRegularity.LocalSobolev Ω 0 (u : Dist) :=
  ElasticityRegularity.MemSobolev.local_zero (memSobolev_zero_iff.mpr ⟨u,rfl⟩) Ω
lemma schwartz_local_nat (Ω : Set X) (u : S) (N : ℕ) :
    ElasticityRegularity.LocalSobolev Ω N (u : Dist) := by
  intro g hg hc _
  exact sobolev_nat_product (EuclideanSpace.basisFun (Fin 3) ℝ) N hg hc u.memSobolev

lemma inverseCoeff_mul (f : Smooth) (hf : ExteriorConstant f) (hn : ∀ x, (f : X → ℂ) x ≠ 0) :
    inverseCoeff f hf hn*exteriorCoeff f hf=1 := by
  apply Subtype.ext
  exact reciprocal_mul f hn

/-- Actual uniform physical weak solvability together with proved interior
smoothness of every cutoff of the physical displacement and shifted divergence.
This combines the supported Carleman/Hahn--Banach construction with the true
augmented distribution identity rather than assuming elliptic regularity. -/
theorem weak_smooth_solvability_oai (R : ℝ) (hR : 1 ≤ R)
    (Ω : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ f : Fin 3 → S, ∃ w : _root_.OAI.ElasticityPhysicalDual.H, ‖w‖ ≤ C*‖embed f‖ ∧
        (∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
          (fun j => (w j : Dist)) i) (f i : Dist)) ∧
        ∀ i : Fin 4, ∀ g : X → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ Ω →
          ∃ v : BoundedContinuousFunction X ℂ, ContDiff ℝ (⊤ : ℕ∞) (v : X → ℂ) ∧
            smulLeftCLM ℂ g ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
              (fun j => (w j : Dist)) : Fin 4 → Dist) i) =
              ((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure X)) : Dist) := by
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := ElasticityPhysicalSolvability.weak_solvability R hR α β hα lam m hl hm hm0 he0
  refine ⟨C,h₀,hC,hh₀,fun h hh hs f => ?_⟩
  obtain ⟨w,hw,hwe⟩ := hsol h hh hs (embed f)
  have heq := weak_to_local_physical Ω R hΩ (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
    hrl hrm w (embed f) hwe
  have heq' : ∀ i, LocalEq Ω (phys (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm)
      (fun j => (w j : Dist)) i) (f i : Dist) := by
    intro i
    simpa only [embed_apply,ElasticityBessel.L2,SchwartzMap.toLpCLM_apply,Lp.toTemperedDistribution_toLp_eq] using heq i
  refine ⟨w,hw,heq',fun i g hg hc hgs => ?_⟩
  let n := inverseCoeff m hm hm0
  let o := inverseCoeff (lam+m+m) ((hl.add hm).add hm) he0
  have hn : n*exteriorCoeff m hm=1 := inverseCoeff_mul m hm hm0
  have ho : o*(exteriorCoeff lam hl+exteriorCoeff m hm+exteriorCoeff m hm)=1 := by
    apply Subtype.ext
    exact reciprocal_mul (lam+m+m) he0
  exact physical_cutoff_smooth (phase h α β) (exteriorCoeff lam hl) (exteriorCoeff m hm) n o hn ho
    (fun j => (w j : Dist)) (fun j => (f j : Dist)) heq' (fun j => lp_local_zero Ω (w j))
    (fun N j => schwartz_local_nat Ω (f j) N) i hg hc hgs
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.weak_smooth_solvability_oai := @OAI.ElasticityDistribution.weak_smooth_solvability_oai
