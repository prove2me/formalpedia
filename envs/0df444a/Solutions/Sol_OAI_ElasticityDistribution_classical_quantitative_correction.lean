-- Prove2me | solution 1 for OAI.ElasticityDistribution.classical_quantitative_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:32:36.725107+00:00
-- url     : https://prove2.me/submissions/1c672977-6ffd-4fe5-9111-822104ca86d7

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityDistribution_physical_quantitative_correction

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

end ElasticitySchwartzCarleman

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

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

end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace LocalEqual
variable {Ω : Set E} {u v w u' v' : 𝓢'(E,ℂ)}
lemma symm (h : LocalEqual Ω u v) : LocalEqual Ω v u := fun φ hc hs => (h φ hc hs).symm
lemma trans (h : LocalEqual Ω u v) (h' : LocalEqual Ω v w) : LocalEqual Ω u w :=
  fun φ hc hs => (h φ hc hs).trans (h' φ hc hs)
lemma cutoff (h : LocalEqual Ω u v) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : E → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : E → ℂ))).trans hs
end LocalEqual
end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_dist_injective : Function.Injective (fun u : 𝓢(E,ℂ) => (u : 𝓢'(E,ℂ))) := by
  intro u v h
  apply SchwartzMap.injective_toLp 2 volume
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) =
    ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ))
  simpa only [Lp.toTemperedDistribution_toLp_eq] using h

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma LocalEqual.cutoff_one {Ω : Set E} (u : 𝓢'(E,ℂ)) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (h1 : Set.EqOn g 1 Ω) :
    LocalEqual Ω (smulLeftCLM ℂ g u) u := by
  intro φ _ hs
  rw [smulLeftCLM_apply_apply]
  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg,smul_eq_mul]
  by_cases hx : φ x=0
  · simp [hx]
  · rw [h1 (hs (subset_tsupport _ hx))]
    simp

lemma LocalEqual.schwartz_eqOn {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : 𝓢(E,ℂ)} (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    Set.EqOn (u : E → ℂ) (v : E → ℂ) Ω := by
  intro x hx
  obtain ⟨g,hs,hc,hg,_,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hΩ.mem_nhds hx)
  let f : E → ℂ := fun y => (g y : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  have hfs : tsupport f ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro y hy
    change g y ≠ 0
    intro hy0
    apply hy
    change (g y : ℂ)=0
    rw [hy0,Complex.ofReal_zero]
  have he := h.cutoff hfg hfc hfs
  rw [distribution_schwartz_product (hfc.hasTemperateGrowth hfg),
    distribution_schwartz_product (hfc.hasTemperateGrowth hfg)] at he
  have he' := congrArg (fun w : 𝓢(E,ℂ) => w x) (schwartz_dist_injective he)
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hfc.hasTemperateGrowth hfg),smul_eq_mul] at he'
  have hx1 : f x=1 := by simp only [f,h1,Complex.ofReal_one]
  simpa only [hx1,one_mul] using he'

lemma smooth_Linfty_product {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (v : BoundedContinuousFunction E ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ)) :
    let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
    smulLeftCLM ℂ g (((v.memLp_top.toLp _ : Lp ℂ ∞ (volume : Measure E))) : 𝓢'(E,ℂ)) = (f : 𝓢'(E,ℂ)) := by
  intro f
  ext φ
  simp only [smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply,SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [v.memLp_top.coeFn_toLp] with x hx
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth hg),hx,smul_eq_mul]
  change g x*φ x*v x = φ x*(g x*v x)
  ring

/-- Interior cutoff regularity yields an actual Schwartz representative on the
smaller open set; this is what is needed to construct physical smooth CGO
solutions on a ball from an L2 weak solution on a larger ball. -/
theorem local_schwartz_representative {Ω Ω' : Set E} (u : 𝓢'(E,ℂ))
    (hu : ∀ N : ℕ, LocalSobolev Ω N u) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : 𝓢(E,ℂ), LocalEqual Ω' u (v : 𝓢'(E,ℂ)) := by
  obtain ⟨v,hv,he⟩ := all_orders_smooth_representative (fun N => hu N g hg hc hs)
  let f : 𝓢(E,ℂ) := (hc.mul_right : HasCompactSupport (g*(v : E → ℂ))).toSchwartzMap (hg.mul hv)
  refine ⟨f,?_⟩
  have he' := smooth_Linfty_product hg hc v hv
  have hlocal := (LocalEqual.cutoff_one u (hc.hasTemperateGrowth hg) h1).symm
  have hlocal' := (LocalEqual.cutoff_one (smulLeftCLM ℂ g u) (hc.hasTemperateGrowth hg) h1).symm
  have h := hlocal.trans hlocal'
  rw [he,he'] at h
  exact h
end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma LocalEqual.lp_ae {Ω : Set E} (hΩ : IsOpen Ω)
    (u v : Lp ℂ 2 (volume : Measure E))
    (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → u x=v x := by
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : E → ℂ) (volume : Measure E) := (Lp.memLp v).locallyIntegrable (by norm_num)
  have he : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → (u x-v x)=0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn Ω) ?_
  · filter_upwards [he] with x hx
    intro hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro g hg hc hs
  let f : E → ℂ := fun x => (g x : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  let φ : 𝓢(E,ℂ) := hfc.toSchwartzMap hfg
  have hfs : tsupport (φ : E → ℂ) ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro x hx hzero
    apply hx
    change (g x : ℂ)=0
    rw [hzero,Complex.ofReal_zero]
  have hh := h φ hfc hfs
  simp only [Lp.toTemperedDistribution_apply] at hh
  have hiu := hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  have hiv := hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  simp only [smul_sub]
  rw [integral_sub hiu hiv,sub_eq_zero]
  simp only [show (φ : E → ℂ)=f from rfl,f,Complex.real_smul,smul_eq_mul] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

/-- The smooth local representative really is the original L2 function almost
 everywhere, so the HB solution's L2 estimate is not lost in regularization. -/
theorem local_schwartz_l2_representative {Ω Ω' : Set E} (hΩ' : IsOpen Ω')
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ N : ℕ, LocalSobolev Ω N (u : 𝓢'(E,ℂ))) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : 𝓢(E,ℂ), LocalEqual Ω' (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) ∧
      ∀ᵐ x ∂(volume : Measure E), x ∈ Ω' → u x=v x := by
  obtain ⟨v,hv⟩ := local_schwartz_representative (u : 𝓢'(E,ℂ)) hu hg hc hs h1
  refine ⟨v,hv,?_⟩
  have he : LocalEqual Ω' (u : 𝓢'(E,ℂ)) ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) := by
    simpa only [Lp.toTemperedDistribution_toLp_eq] using hv
  filter_upwards [LocalEqual.lp_ae hΩ' u (v.toLp 2 volume) he,v.coeFn_toLp 2 volume] with x hx hxv
  intro hxΩ
  exact (hx hxΩ).trans hxv
end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal
namespace ElasticityDistribution
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma coe_schwartz_add (u v : S) : ((u+v : S) : Dist)=(u : Dist)+(v : Dist) := map_add _ _ _
lemma coe_schwartz_smul (c : ℂ) (u : S) : ((c • u : S) : Dist)=c • (u : Dist) := map_smul _ _ _
lemma coe_schwartz_sum {ι : Type*} (s : Finset ι) (u : ι → S) :
    ((∑ i ∈ s, u i : S) : Dist)=∑ i ∈ s, (u i : Dist) := map_sum _ _ _
lemma sd_schwartz (z : Fin 3 → ℂ) (i : Fin 3) (u : S) :
    sd z i (u : Dist)=(shiftD z i u : Dist) := by
  rw [sd_apply,dd_apply,shiftD_apply,coe_schwartz_add,coe_schwartz_smul]
  congr 1
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq u (e i)
lemma coeff_schwartz (a : Coeff) (u : S) : a • (u : Dist)=(mult (eval a) u : Dist) :=
  ElasticityRegularity.distribution_schwartz_product (growth a) u
lemma divd_schwartz (z : Fin 3 → ℂ) (u : Fin 3 → S) :
    divd z (fun i => (u i : Dist))=(∑ i, shiftD z i (u i) : S) := by
  rw [divd,coe_schwartz_sum]
  simp only [sd_schwartz]
lemma phys_schwartz (z : Fin 3 → ℂ) (lam m : Coeff) (u : Fin 3 → S) (i : Fin 3) :
    phys z lam m (fun j => (u j : Dist)) i=(physical z (eval lam) (eval m) u i : Dist) := by
  simp only [phys,physical,divd_schwartz,sd_schwartz,← coe_schwartz_add,
    coeff_schwartz,← coe_schwartz_sum]

lemma LocalEq.physical {Ω : Set X} {u v : Fin 3 → Dist} (h : ∀ i, LocalEq Ω (u i) (v i))
    (z : Fin 3 → ℂ) (lam m : Coeff) (i : Fin 3) :
    LocalEq Ω (phys z lam m u i) (phys z lam m v i) :=
  (((LocalEq.divergence h z).coeff lam).shifted z i).add (LocalEq.sum Finset.univ
    (fun j _ => (((h i).shifted z j).add ((h j).shifted z i) |>.coeff m).shifted z j))

/-- A genuinely classical physical solution on an interior open set is obtained
from the actual weak solution, and represents that same L2 unknown there. -/
theorem classical_representative {Ω Ω' : Set X} (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (z : Fin 3 → ℂ) (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (w : ElasticityPhysicalDual.H) (F : Fin 3 → S)
    (heq : ∀ i, LocalEq Ω (phys z lam m (fun j => (w j : Dist)) i) (F i : Dist))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : Fin 3 → S, (∀ i, ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v i x) ∧
      ∀ i, Set.EqOn (physical z (eval lam) (eval m) v i : X → ℂ) (F i : X → ℂ) Ω' := by
  have hall := physical_local_all_orders z lam m n o hn ho (fun j => (w j : Dist))
    (fun j => (F j : Dist)) heq (fun j => lp_local_zero Ω (w j)) (fun N j => schwartz_local_nat Ω (F j) N)
  have hv : ∀ i : Fin 3, ∃ v : S, ElasticityRegularity.LocalEqual Ω' (w i : Dist) (v : Dist) ∧
      ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v x := by
    intro i
    exact ElasticityRegularity.local_schwartz_l2_representative hΩ' (w i)
      (fun N => hall N i.succ) hg hc hs h1
  choose v hv he using hv
  refine ⟨v,he,fun i => ?_⟩
  apply ElasticityRegularity.LocalEqual.schwartz_eqOn hΩ'
  have hl : ∀ j, LocalEq Ω' (w j : Dist) (v j : Dist) := hv
  have hphys := LocalEq.physical hl z lam m i
  rw [phys_schwartz] at hphys
  exact fun φ hφ hφs => (hphys φ hφ hφs).symm.trans (heq i φ hφ (hφs.trans hsub))
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds

open ElasticityPhysicalAlgebra (phase physical)

/-- The quantitative correction and classical representative are the SAME
physical solution. In particular no smooth solvability estimate is postulated. -/
theorem classical_quantitative_correction_oai (R : ℝ) (hR : 1≤R)
    (Ω Ω' : Set X) (hΩ : Ω ⊆ Metric.closedBall 0 R) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (α β : X) (hα : α ≠ 0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x, star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x, star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x, (m : X → ℂ) x ≠ 0)
    (he0 : ∀ x, ((lam+m+m : Smooth) : X → ℂ) x ≠ 0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i, HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4, Set.EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i, tsupport (χ i) ⊆ Ω) (h1 : Set.EqOn (χ 0) 1 Ω') :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ, 0<h → h≤h₀ →
      ∀ f : Fin 3 → S, ∃ w : ElasticityPhysicalDual.H, ∃ q : HV, ∃ v : Fin 3 → S,
        (∀ i, ∀ᵐ x ∂(volume : Measure X), x ∈ Ω' → w i x=v i x) ∧
        (∀ i, Set.EqOn (physical (phase h α β) (eval (exteriorCoeff lam hl))
          (eval (exteriorCoeff m hm)) v i : X → ℂ) (f i : X → ℂ) Ω') ∧
        (∀ i, sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖ ≤ C*‖ElasticityPhysicalDual.embed f‖ ∧
        ‖q‖ ≤ C*h⁻¹^6*‖ElasticityPhysicalDual.embed f‖ := by
  obtain ⟨C,h₀,hC,hh₀,hsol⟩ := physical_quantitative_correction R hR Ω hΩ α β hα
    lam m hl hm hrl hrm hm0 he0 χ hχ hcχ hnest hs
  refine ⟨C,h₀,hC,hh₀,fun h hh hsmall f => ?_⟩
  obtain ⟨w,q,heq,hq,hw,hqn⟩ := hsol h hh hsmall f
  let n := inverseCoeff m hm hm0
  let o := inverseCoeff (lam+m+m) ((hl.add hm).add hm) he0
  have hn : n*exteriorCoeff m hm=1 := inverseCoeff_mul m hm hm0
  have ho : o*(exteriorCoeff lam hl+exteriorCoeff m hm+exteriorCoeff m hm)=1 := by
    apply Subtype.ext
    exact reciprocal_mul (lam+m+m) he0
  obtain ⟨v,hv,hphys⟩ := classical_representative hΩ' hsub (phase h α β)
    (exteriorCoeff lam hl) (exteriorCoeff m hm) n o hn ho w f heq (hχ 0) (hcχ 0) (hs 0) h1
  exact ⟨w,q,v,hv,hphys,hq,hw,hqn⟩
end ElasticityDistribution

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityDistribution.classical_quantitative_correction_oai := @OAI.ElasticityDistribution.classical_quantitative_correction_oai
