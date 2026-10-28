-- Prove2me | solution 1 for OAI.Elasticity.physical_classical_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:02:19.082746+00:00
-- url     : https://prove2.me/submissions/e3b340a1-1c10-4953-a8cf-56bfbc974388

import Mathlib
import Definitions.Def_ElasticityUniqueness
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

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

end

end ElasticityNegativeOrder

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
lemma trans (h : LocalEq Ω u v) (h' : LocalEq Ω v w) : LocalEq Ω u w :=
  fun φ hc hs => (h φ hc hs).trans (h' φ hc hs)
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
namespace ElasticityDistribution

section

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder

open ElasticityAugmented TemperedDistribution
open ElasticityPhysicalAlgebra (shiftD shiftD_apply)
open ElasticityNegativeOrder (mult)

lemma coeff_test (a : Coeff) (u : Dist) (φ : S) :
    (a • u) φ = u (mult (eval a) φ) := rfl

end

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder

end ElasticityDistribution

open scoped BigOperators

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
-- module Solutions.OAIQ6_Elast.Elasticity_Variational
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

theorem dirichlet_unique (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u v : H1 Ω)
    (hu : WeakSolution Ω lam mu u) (hv : WeakSolution Ω lam mu v)
    (ht : trace Ω u=trace Ω v) : u=v := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  let u' := (h1Equiv Ω).symm u
  let v' := (h1Equiv Ω).symm v
  have htu : SameTrace Ω (h1Equiv Ω u') (h1Equiv Ω v') := by
    simpa only [u',v',Equiv.apply_symm_apply] using (trace_eq_iff u v).mp ht
  let z : H10Hilbert Ω := ⟨u'.val-v'.val,(sameTrace_h1Equiv u' v').mp htu⟩
  have hu' : ∀ w : H10Hilbert Ω, jetEnergy hl hm u'.val w.val=0 :=
    (weakSolution_h1Equiv hl hm u').mp (by simpa only [u',Equiv.apply_symm_apply] using hu)
  have hv' : ∀ w : H10Hilbert Ω, jetEnergy hl hm v'.val w.val=0 :=
    (weakSolution_h1Equiv hl hm v').mp (by simpa only [v',Equiv.apply_symm_apply] using hv)
  have hz : zeroTraceEnergy hl hm z z=0 := by
    change jetEnergy hl hm (u'.val-v'.val) z.val=0
    rw [map_sub (jetEnergy hl hm) u'.val v'.val,sub_apply,hu',hv',sub_self]
  obtain ⟨c,hc,hbound⟩ := physical_coercive ha hO hB
  have hn : ‖z‖=0 := by
    have hh := hbound z
    rw [hz] at hh
    have hs : ‖z‖*‖z‖ ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by nlinarith only [hh])
    nlinarith [norm_nonneg z]
  have he : u'=v' := by
    apply Subtype.ext
    have hval := congrArg Subtype.val (norm_eq_zero.mp hn)
    change u'.val-v'.val=0 at hval
    exact sub_eq_zero.mp hval
  exact (h1Equiv Ω).symm.injective he

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

lemma energy_eq_of_sameTrace (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    {u v w : H1 Ω} (hu : WeakSolution Ω lam mu u) (hvw : SameTrace Ω v w) :
    energy Ω lam mu u v=energy Ω lam mu u w := by
  let u' := (h1Equiv Ω).symm u
  let v' := (h1Equiv Ω).symm v
  let w' := (h1Equiv Ω).symm w
  have ht : v'.val-w'.val ∈ H10Hilbert Ω :=
    (sameTrace_h1Equiv v' w').mp (by simpa only [v',w',Equiv.apply_symm_apply] using hvw)
  have he := (weakSolution_h1Equiv hl hm u').mp (by
    simpa only [u',Equiv.apply_symm_apply] using hu) ⟨v'.val-w'.val,ht⟩
  change jetEnergy hl hm u'.val (v'.val-w'.val)=0 at he
  rw [map_sub] at he
  have hv' := jetEnergy_eq_energy hl hm u' v'
  have hw' := jetEnergy_eq_energy hl hm u' w'
  simp only [u',v',w',Equiv.apply_symm_apply] at hv' hw'
  rw [hv',hw'] at he
  exact sub_eq_zero.mp he

lemma DN_eq_energy (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) (v : H1 Ω) :
    DN Ω lam mu f (trace Ω v)=energy Ω lam mu (dirichletSolution Ω lam mu f) v := by
  apply energy_eq_of_sameTrace (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) (dirichletSolution_spec ha hO hB f).2
  apply (trace_eq_iff _ _).mp
  exact Quot.out_eq (trace Ω v)

lemma solution_eq_dirichlet (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) {u : H1 Ω} (hu : WeakSolution Ω lam mu u) :
    u=dirichletSolution Ω lam mu (trace Ω u) :=
  dirichlet_unique ha hO hB _ _ hu (dirichletSolution_spec ha hO hB _).2
    (dirichletSolution_spec ha hO hB _).1.symm

theorem interior_physical_transfer {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    {u₁ : H1 Ω} (hu₁ : WeakSolution Ω lam₁ mu₁ u₁) :
    ∃ u₂ : H1 Ω, WeakSolution Ω lam₂ mu₂ u₂ ∧ trace Ω u₂=trace Ω u₁ ∧
      ∀ v : H1 Ω, energy Ω lam₂ mu₂ u₂ v=energy Ω lam₁ mu₁ u₁ v := by
  let u₂ := dirichletSolution Ω lam₂ mu₂ (trace Ω u₁)
  have hs := dirichletSolution_spec ha₂ hO hB (trace Ω u₁)
  refine ⟨u₂,hs.2,hs.1,?_⟩
  intro v
  rw [← DN_eq_energy ha₂ hO hB,← hDN,DN_eq_energy ha₁ hO hB]
  rw [← solution_eq_dirichlet ha₁ hO hB hu₁]

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Restriction
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω B : Set X}
lemma energy_eq_ambient (lam mu : X → ℝ) (u v : H1 Ω) :
    energy Ω lam mu u v=ambientEnergy lam mu u.val v.val := rfl
lemma elasticDensity_symm (a b : ℝ) (P Q : Fin 3 → V) :
    elasticDensity a b P Q=elasticDensity a b Q P := by
  unfold elasticDensity
  have hs : (∑ i, ∑ j, ((P j i+P i j)/2)*((Q j i+Q i j)/2))=
      ∑ i, ∑ j, ((Q j i+Q i j)/2)*((P j i+P i j)/2) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hs]
  ring
lemma gradient_restrict (h : Ω⊆B) (u : Ambient B) :
    (fun x => gradient (ambientRestrict h u) x)=ᵐ[volume.restrict Ω] gradient u := by
  have he := Filter.eventually_all.mpr (fun i : Fin 3 => lpRestrictBetween_coe h (u.2 i))
  filter_upwards [he] with x hx
  exact funext hx
lemma gradient_extend (hΩ : MeasurableSet Ω) (u : Ambient Ω) :
    (fun x => gradient (ambientExtend (B := B) hΩ u) x)=ᵐ[volume.restrict B] Ω.indicator (gradient u) := by
  have he := Filter.eventually_all.mpr (fun i : Fin 3 => lpExtendBetween_coe (B := B) hΩ (u.2 i))
  filter_upwards [he] with x hx
  by_cases hm : x∈Ω
  · rw [indicator_of_mem hm]
    funext i
    exact (hx i).trans (indicator_of_mem hm _)
  · rw [indicator_of_notMem hm]
    funext i
    exact (hx i).trans (indicator_of_notMem hm _)
lemma ambientDensity_integrable {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : Ambient Ω) :
    Integrable (ambientDensity lam mu u v) (volume.restrict Ω) := by
  have hd (w : Ambient Ω) : MemLp (fun x => ∑ i, w.2 i x i) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun i _ => entry_memLp w i i)
  have hs (w : Ambient Ω) (i j : Fin 3) :
      MemLp (fun x => (w.2 j x i+w.2 i x j)/2) 2 (volume.restrict Ω) :=
    by simpa only [div_eq_mul_inv,Pi.add_apply] using
      ((entry_memLp w i j).add (entry_memLp w j i)).mul_const (2 : ℝ)⁻¹
  have hL := (hl.mul_memLp_fun (hd u)).integrable_mul (hd v)
  have hS (i j) := (hm.mul_memLp_fun (hs u i j)).integrable_mul (hs v i j)
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hS i j))
  apply (hL.add (hsum.const_mul 2)).congr
  exact Filter.Eventually.of_forall (fun x => by
    simp only [ambientDensity,elasticDensity,gradient,Pi.mul_apply,Pi.add_apply,Finset.mul_sum,mul_assoc])
lemma ambientEnergy_symm (lam mu : X → ℝ) (u v : Ambient Ω) :
    ambientEnergy lam mu u v=ambientEnergy lam mu v u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => elasticDensity_symm _ _ _ _)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω B : Set X}
lemma ambientEnergy_extend_right (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (lam mu : X → ℝ) (u : Ambient B) (v : Ambient Ω) :
    ambientEnergy lam mu u (ambientExtend hΩ v)=
      ambientEnergy lam mu (ambientRestrict h u) v := by
  let f := fun x => elasticDensity (lam x) (mu x) (gradient u x) (gradient v x)
  calc
    _ = ∫ x, Ω.indicator f x ∂(volume.restrict B) := by
      apply integral_congr_ae
      filter_upwards [gradient_extend (B := B) hΩ v] with x hx
      change elasticDensity _ _ _ _=_
      rw [hx]
      by_cases hm : x∈Ω
      · simp only [indicator_of_mem hm]
        rfl
      · simp only [indicator_of_notMem hm,elasticDensity_zero_right]
    _ = ∫ x, f x ∂(volume.restrict Ω) := by
      rw [integral_indicator hΩ,Measure.restrict_restrict hΩ,inter_eq_left.mpr h]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [gradient_restrict h u] with x hx
      exact congrArg (fun P => elasticDensity (lam x) (mu x) P (gradient v x)) hx.symm
lemma ambientEnergy_extend_left (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (lam mu : X → ℝ) (u : Ambient Ω) (v : Ambient B) :
    ambientEnergy lam mu (ambientExtend hΩ u) v=
      ambientEnergy lam mu u (ambientRestrict h v) := by
  rw [ambientEnergy_symm,ambientEnergy_extend_right hΩ h,ambientEnergy_symm]
lemma BoundedCoefficient.restrict {a : X → ℝ} (ha : BoundedCoefficient B a) (h : Ω⊆B) :
    BoundedCoefficient Ω a := by
  have hm : volume.restrict Ω≤volume.restrict B := Measure.restrict_mono h (le_refl (volume : Measure X))
  refine ⟨ha.measurable.mono_measure hm,?_⟩
  obtain ⟨C,hC⟩ := ha.bound
  exact ⟨C,ae_mono hm hC⟩
lemma energy_coefficient_locality {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (hΩ : MeasurableSet Ω) (h : Ω⊆B)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x) (u v : Ambient B) :
    ambientEnergy lam₂ mu₂ u v-ambientEnergy lam₁ mu₁ u v=
      ambientEnergy lam₂ mu₂ (ambientRestrict h u) (ambientRestrict h v)-
      ambientEnergy lam₁ mu₁ (ambientRestrict h u) (ambientRestrict h v) := by
  let f := fun x => ambientDensity lam₂ mu₂ u v x-ambientDensity lam₁ mu₁ u v x
  calc
    _ = ∫ x, f x ∂(volume.restrict B) := (integral_sub
      (ambientDensity_integrable hl₂ hm₂ u v) (ambientDensity_integrable hl₁ hm₁ u v)).symm
    _ = ∫ x, Ω.indicator f x ∂(volume.restrict B) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x∈Ω
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          dsimp [f,ambientDensity]
          rw [(he x hx).1,(he x hx).2,sub_self])
    _ = ∫ x, f x ∂(volume.restrict Ω) := by
      rw [integral_indicator hΩ,Measure.restrict_restrict hΩ,inter_eq_left.mpr h]
    _ = ∫ x, ambientDensity lam₂ mu₂ (ambientRestrict h u) (ambientRestrict h v) x-
        ambientDensity lam₁ mu₁ (ambientRestrict h u) (ambientRestrict h v) x ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [gradient_restrict h u,gradient_restrict h v] with x hu hv
      simp only [f,ambientDensity,hu,hv]
    _ = _ := integral_sub (ambientDensity_integrable (hl₂.restrict h) (hm₂.restrict h) _ _)
      (ambientDensity_integrable (hl₁.restrict h) (hm₁.restrict h) _ _)
lemma elasticDensity_add_left (a b : ℝ) (P Q R : Fin 3 → V) :
    elasticDensity a b (P+Q) R=elasticDensity a b P R+elasticDensity a b Q R := by
  simp only [elasticDensity,Pi.add_apply,PiLp.add_apply]
  have he (i j : Fin 3) : ((P j i+Q j i+(P i j+Q i j))/2)*((R j i+R i j)/2)=
      ((P j i+P i j)/2)*((R j i+R i j)/2)+((Q j i+Q i j)/2)*((R j i+R i j)/2) := by ring
  simp only [he,Finset.sum_add_distrib]
  ring
lemma gradient_add (u v : Ambient Ω) :
    gradient (u+v)=ᵐ[volume.restrict Ω] fun x => gradient u x+gradient v x := by
  have he := Filter.eventually_all.mpr (fun i : Fin 3 => Lp.coeFn_add (u.2 i) (v.2 i))
  filter_upwards [he] with x hx
  exact funext hx
lemma ambientEnergy_add_left {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v w : Ambient Ω) :
    ambientEnergy lam mu (u+v) w=ambientEnergy lam mu u w+ambientEnergy lam mu v w := by
  rw [ambientEnergy,ambientEnergy,ambientEnergy,← integral_add
    (ambientDensity_integrable hl hm u w) (ambientDensity_integrable hl hm v w)]
  apply integral_congr_ae
  filter_upwards [gradient_add u v] with x hx
  change elasticDensity _ _ _ _=_
  rw [hx,elasticDensity_add_left]
  rfl
lemma ambientEnergy_sub_left {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v w : Ambient Ω) :
    ambientEnergy lam mu (u-v) w=ambientEnergy lam mu u w-ambientEnergy lam mu v w := by
  have he := ambientEnergy_add_left hl hm (u-v) v w
  rw [sub_add_cancel] at he
  linarith
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
namespace Elasticity
variable {Ω B : Set X}
lemma weakSolution_restrict (hΩ : MeasurableSet Ω) (h : Ω⊆B) {lam mu : X → ℝ}
    {u : H1 B} (hu : WeakSolution B lam mu u) : WeakSolution Ω lam mu (h1Restrict h u) := by
  intro v hv
  have he := hu (h1Extend hΩ h v hv) (extend_h10 hΩ h hv)
  change ambientEnergy lam mu u.val (ambientExtend hΩ v.val)=0 at he
  rw [ambientEnergy_extend_right hΩ h] at he
  exact he
lemma gluedH1_exterior_gradient (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) :
    ∀ᵐ x ∂(volume.restrict B), x∉Ω → gradient (gluedH1 hΩ h u v ht).val x=gradient u.val x := by
  filter_upwards [gradient_add u.val (ambientExtend (B := B) hΩ (v.val-ambientRestrict h u.val)),
    gradient_extend (B := B) hΩ (v.val-ambientRestrict h u.val)] with x ha he hx
  change gradient (u.val+ambientExtend hΩ (v.val-ambientRestrict h u.val)) x=_
  rw [ha,he,indicator_of_notMem hx,add_zero]
lemma gluedH1_exterior_value (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) :
    ∀ᵐ x ∂(volume.restrict B), x∉Ω → (gluedH1 hΩ h u v ht).val.1 x=u.val.1 x := by
  filter_upwards [Lp.coeFn_add u.val.1 (lpExtendBetween (B := B) hΩ (v.val-ambientRestrict h u.val).1),
    lpExtendBetween_coe (B := B) hΩ (v.val-ambientRestrict h u.val).1] with x ha he hx
  change (u.val.1+lpExtendBetween hΩ (v.val-ambientRestrict h u.val).1 : Lp V 2 (volume.restrict B)) x=_
  rw [ha]
  change u.val.1 x+lpExtendBetween hΩ (v.val-ambientRestrict h u.val).1 x=_
  rw [he,indicator_of_notMem hx,add_zero]

theorem physical_weak_transfer {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hO : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (h : Ω⊆B)
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    {u : H1 B} (hu : WeakSolution B lam₁ mu₁ u) :
    ∃ v : H1 B, WeakSolution B lam₂ mu₂ v ∧
      (∀ᵐ x ∂(volume.restrict B), x∉Ω → v.val.1 x=u.val.1 x) ∧
      (∀ᵐ x ∂(volume.restrict B), x∉Ω → gradient v.val x=gradient u.val x) := by
  obtain ⟨v,hv,ht,hpair⟩ := interior_physical_transfer ha₁ ha₂ hO hOB hDN
    (weakSolution_restrict hO.measurableSet h hu)
  have ht' : SameTrace Ω v (h1Restrict h u) := (trace_eq_iff _ _).mp ht
  refine ⟨gluedH1 hO.measurableSet h u v ht',?_,
    gluedH1_exterior_value hO.measurableSet h u v ht',
    gluedH1_exterior_gradient hO.measurableSet h u v ht'⟩
  intro w hw
  have hw0 := hu w hw
  have hp := hpair (h1Restrict h w)
  simp only [energy_eq_ambient] at hp hw0 ⊢
  change ambientEnergy lam₂ mu₂ (u.val+ambientExtend hO.measurableSet
    (v.val-ambientRestrict h u.val)) w.val=0
  rw [ambientEnergy_add_left hl₂ hm₂,ambientEnergy_extend_left hO.measurableSet h,
    ambientEnergy_sub_left (hl₂.restrict h) (hm₂.restrict h)]
  have hc := energy_coefficient_locality hl₁ hm₁ hl₂ hm₂ hO.measurableSet h he u.val w.val
  change ambientEnergy lam₂ mu₂ v.val (ambientRestrict h w.val)=
    ambientEnergy lam₁ mu₁ (ambientRestrict h u.val) (ambientRestrict h w.val) at hp
  linarith
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}
lemma ambientScalar_ae (u : Ambient Ω) (k : Option (Fin 3)) (i : Fin 3) :
    ambientScalar Ω k i u =ᵐ[volume.restrict Ω] fun x => ((jetEquiv Ω).symm u k x) i :=
  jetScalar_ae _ _ _
lemma scalar_pair_smooth {f : X → V} (hf : MemLp f 2 (volume.restrict Ω))
    (g : SchwartzMap X ℝ) (i : Fin 3) :
    inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (hf.toLp f))
      (schwartzR Ω g) = ∫ x, (f x) i*g x ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i) (hf.toLp f),
    hf.coeFn_toLp,g.coeFn_toLp 2 (volume.restrict Ω)] with x hx hy hz
  change inner ℝ (((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (hf.toLp f)) x) (g.toLp 2 (volume.restrict Ω) x)=_
  rw [hx,hz,hy]
  exact real_inner_comm _ _
lemma smooth_ibp {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ) ⊆ Ω) (j : Fin 3) :
    (∫ x, f x*ElasticityKorn.d (coordVector j) g x ∂(volume.restrict Ω)) =
    -(∫ x, fderiv ℝ f x (coordVector j)*g x ∂(volume.restrict Ω)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (g : X → ℝ) := g.smooth _
  have hd : Continuous (fun x => fderiv ℝ f x (coordVector j)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun x => fderiv ℝ (g : X → ℝ) x (coordVector j)) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hz := image_eq_zero_of_notMem_tsupport (f := (ElasticityKorn.d (coordVector j) g : X → ℝ))
      (fun ht => hx (hs ((tsupport_fderiv_apply_subset ℝ (coordVector j)) ht)))
    rw [hz,mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (f := (g : X → ℝ)) (fun ht => hx (hs ht)),mul_zero])]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hd.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    ((hf.continuous.mul hgd).integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ _).mul_left))
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hc.mul_left))
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

lemma weakDerivativePair_smooth (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ) ⊆ Ω) (i j : Fin 3) {u : Ambient Ω} (hu : u∈SmoothJets Ω) :
    weakDerivativePair Ω g i j u=0 := by
  obtain ⟨f,hf,hd,hsm,hu,huj⟩ := hu
  have he0 : ambientScalar Ω none i u=
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (hf.toLp f) := by
    change (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) u.1=_
    rw [hu]
  have he1 : ambientScalar Ω (some j) i u=
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) ((hd j).toLp (coordDeriv f j)) := by
    change (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) (u.2 j)=_
    rw [huj]
  simp only [weakDerivativePair,add_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,he0,he1]
  rw [← real_inner_comm (schwartzR Ω (ElasticityKorn.d (coordVector j) g)),
    ← real_inner_comm (schwartzR Ω g),scalar_pair_smooth,scalar_pair_smooth]
  have hh := smooth_ibp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hsm) g hc hs j
  change (∫ x, (f x) i * ElasticityKorn.d (coordVector j) g x ∂(volume.restrict Ω)) =
    -(∫ x, fderiv ℝ (fun y => (f y) i) x (coordVector j) * g x ∂(volume.restrict Ω)) at hh
  simp only [coordDeriv_scalar f hsm] at hh
  rw [hh,neg_add_cancel]
/-- The gradient components in the closure-of-jets H1 really are weak
partial derivatives of its value. No weak-derivative property is assumed. -/
theorem h1_weak_derivative (u : H1 Ω) (g : SchwartzMap X ℝ)
    (hc : HasCompactSupport (g : X → ℝ)) (hs : tsupport (g : X → ℝ) ⊆ Ω)
    (i j : Fin 3) :
    inner ℝ (ambientScalar Ω none i u.val) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)) =
      -inner ℝ (ambientScalar Ω (some j) i u.val) (schwartzR Ω g) := by
  have hm : MapsTo (weakDerivativePair Ω g i j) (SmoothJets Ω) ({0} : Set ℝ) :=
    fun _ hu => weakDerivativePair_smooth g hc hs i j hu
  have hh := hm.closure (weakDerivativePair Ω g i j).continuous u.property
  rw [closure_singleton] at hh
  change weakDerivativePair Ω g i j u.val=0 at hh
  simp only [weakDerivativePair,add_apply,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] at hh
  rw [← real_inner_comm (schwartzR Ω (ElasticityKorn.d (coordVector j) g)),
    ← real_inner_comm (schwartzR Ω g)] at hh
  linarith
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}
lemma testField_deriv (g : SchwartzMap X ℝ) (i j : Fin 3) :
    coordDeriv (testField g i) j=fun x => ElasticityKorn.d (coordVector j) g x • coordVector i := by
  funext x
  have h := ((ContinuousLinearMap.toSpanSingleton ℝ (coordVector i)).hasFDerivAt (x := g x)).comp x
    (g.differentiableAt (x := x)).hasFDerivAt
  change fderiv ℝ ((ContinuousLinearMap.toSpanSingleton ℝ (coordVector i)) ∘ (g : X → ℝ)) x (coordVector j)=_
  rw [h.fderiv]
  rfl
lemma testH1_zeroTrace (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) : HasZeroTrace Ω (testH1 g hc hs i) :=
  subset_closure (testFieldJet_mem g hc hs i)
lemma testH1_gradient (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    ∀ᵐ x ∂(volume.restrict Ω), gradient (testH1 g hc hs i).val x=
      fun j => ElasticityKorn.d (coordVector j) g x • coordVector i := by
  have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ j, (testFieldJet (Ω := Ω) g hc i).2 j x=coordDeriv (testField g i) j x :=
    Filter.eventually_all.mpr (fun j => (testField_deriv_memLp g hc i j).coeFn_toLp)
  filter_upwards [he] with x hx
  funext j
  change (testFieldJet (Ω := Ω) g hc i).2 j x=_
  rw [hx,testField_deriv]
lemma density_single (a b : ℝ) (P : Fin 3 → V) (v : Fin 3 → ℝ) (i : Fin 3) :
    elasticDensity a b P (fun j => v j • coordVector i)=
      a*(∑ k, P k k)*v i+b*∑ j, (P j i+P i j)*v j := by
  fin_cases i <;> simp [elasticDensity,Fin.sum_univ_succ,coordVector] <;> ring
end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakSolutions
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory SchwartzMap Set TemperedDistribution
open scoped SchwartzMap LineDeriv
namespace Elasticity
variable {Ω : Set X}
lemma realTest_d (g : SchwartzMap X ℝ) (j : Fin 3) :
    ∂_{coordVector j} (realTest g)=realTest (ElasticityKorn.d (coordVector j) g) := by
  ext x
  change fderiv ℝ ((Complex.ofRealCLM : ℝ → ℂ) ∘ (g : X → ℝ)) x (coordVector j)=
    Complex.ofRealCLM (fderiv ℝ (g : X → ℝ) x (coordVector j))
  rw [((Complex.ofRealCLM.hasFDerivAt (x := g x)).comp x
    (g.differentiableAt (x := x)).hasFDerivAt).fderiv]
  rfl
lemma test_parts (g : SchwartzMap X ℂ) : g=realTest (reTest g)+Complex.I • realTest (imTest g) := by
  ext x
  change g x=↑((g x).re)+Complex.I*↑((g x).im)
  exact (Complex.re_add_im (g x)).symm.trans (by ring)
lemma scalarDistribution_real (f : ScalarL2 Ω) (g : SchwartzMap X ℝ) :
    scalarDistribution Ω f (realTest g)=↑(inner ℝ f (schwartzR Ω g)) := by
  have hi : Integrable (fun x => g x*f x) (volume.restrict Ω) := by
    apply (L2.integrable_inner (𝕜 := ℝ) f (schwartzR Ω g)).congr
    filter_upwards [g.coeFn_toLp 2 (volume.restrict Ω)] with x hx
    change inner ℝ (f x) (g.toLp 2 (volume.restrict Ω) x)=_
    rw [hx]
    rfl
  have hpair : inner ℝ f (schwartzR Ω g)=∫ x, g x*f x ∂(volume.restrict Ω) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [g.coeFn_toLp 2 (volume.restrict Ω)] with x hx
    change inner ℝ (f x) (g.toLp 2 (volume.restrict Ω) x)=_
    rw [hx]
    rfl
  change Lp.toTemperedDistribution (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f) (realTest g)=_
  rw [Lp.toTemperedDistribution_apply,hpair]
  calc
    _ = ∫ x, Complex.ofRealCLM (g x*f x) ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f] with x hx
      rw [hx]
      change (g x : ℂ)*(f x : ℂ)=↑(g x*f x)
      exact (Complex.ofReal_mul _ _).symm
    _ = _ := Complex.ofRealCLM.integral_comp_comm hi
lemma localEq_of_realTest {U V : ElasticityDistribution.Dist}
    (h : ∀ (g : SchwartzMap X ℝ), HasCompactSupport (g : X → ℝ) → tsupport (g : X → ℝ)⊆Ω →
      U (realTest g)=V (realTest g)) : ElasticityDistribution.LocalEq Ω U V := by
  intro φ hc hs
  have hrc : HasCompactSupport (reTest φ : X → ℝ) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (imTest φ : X → ℝ) := hc.comp_left (g := Complex.im) rfl
  have hrs : tsupport (reTest φ : X → ℝ)⊆Ω := (tsupport_comp_subset (g := Complex.re) rfl (φ : X → ℂ)).trans hs
  have his : tsupport (imTest φ : X → ℝ)⊆Ω := (tsupport_comp_subset (g := Complex.im) rfl (φ : X → ℂ)).trans hs
  conv_lhs => rw [test_parts φ]
  conv_rhs => rw [test_parts φ]
  rw [map_add,map_add,map_smul,map_smul,h (reTest φ) hrc hrs,h (imTest φ) hic his]
/-- Actual distributional identification of every H1 gradient. -/
theorem h1_distribution_derivative (u : H1 Ω) (i j : Fin 3) :
    ElasticityDistribution.LocalEq Ω (ElasticityDistribution.dd j (h1Distribution u i))
      (h1GradientDistribution u i j) := by
  apply localEq_of_realTest
  intro g hc hs
  change (∂_{coordVector j} (h1Distribution u i)) (realTest g)=_
  rw [lineDerivOp_apply_apply,realTest_d,map_neg]
  change -scalarDistribution Ω (ambientScalar Ω none i u.val) (realTest (ElasticityKorn.d (coordVector j) g))=
    scalarDistribution Ω (ambientScalar Ω (some j) i u.val) (realTest g)
  rw [scalarDistribution_real,scalarDistribution_real,h1_weak_derivative u g hc hs i j,
    Complex.ofReal_neg,neg_neg]
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}
lemma stressL2_ae (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : stressL2 hl hm u i j =ᵐ[volume.restrict Ω] stressFun lam mu u i j :=
  (stress_memLp hl hm u i j).coeFn_toLp
lemma stress_pair (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) (g : SchwartzMap X ℝ) :
    inner ℝ (stressL2 hl hm u i j) (schwartzR Ω g)=
      ∫ x, stressFun lam mu u i j x*g x ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [stressL2_ae hl hm u i j,g.coeFn_toLp 2 (volume.restrict Ω)] with x hx hy
  change inner ℝ (stressL2 hl hm u i j x) (g.toLp 2 (volume.restrict Ω) x)=_
  rw [hx,hy,real_inner_comm]
  rfl
lemma stress_pair_integrable (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) (g : SchwartzMap X ℝ) :
    Integrable (fun x => stressFun lam mu u i j x*g x) (volume.restrict Ω) :=
  (stress_memLp hl hm u i j).integrable_mul (g.memLp 2 (volume.restrict Ω))
lemma density_stress (a b : ℝ) (u : Fin 3 → V) (v : Fin 3 → ℝ) (i : Fin 3) :
    elasticDensity a b u (fun j => v j • coordVector i)=
      ∑ j, ((if i=j then a*(∑ k, u k k) else 0)+b*(u j i+u i j))*v j := by
  rw [density_single]
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,mul_add,add_mul,Finset.sum_add_distrib,mul_assoc]
lemma energy_test_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    energy Ω lam mu u (testH1 g hc hs i)=
      ∑ j, inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)) := by
  simp only [stress_pair]
  rw [← integral_finsetSum _ (fun j _ => stress_pair_integrable hl hm u.val i j _)]
  change (∫ x, elasticDensity (lam x) (mu x) (gradient u.val x) (gradient (testH1 g hc hs i).val x) ∂(volume.restrict Ω))=_
  apply integral_congr_ae
  filter_upwards [testH1_gradient g hc hs i] with x hx
  rw [hx,density_stress]
  rfl
/-- The variational equation yields the actual scalar-test stress equation. -/
theorem weakSolution_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u) (g : SchwartzMap X ℝ)
    (hc : HasCompactSupport (g : X → ℝ)) (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    (∑ j, inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0 := by
  rw [← energy_test_stress hl hm u g hc hs i]
  exact hu _ (testH1_zeroTrace g hc hs i)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma scalarDistribution_apply (f : ScalarL2 Ω) (g : SchwartzMap X ℂ) :
    scalarDistribution Ω f g=∫ x, g x*(f x : ℂ) ∂(volume.restrict Ω) := by
  change Lp.toTemperedDistribution (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f) g=_
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f] with x hx
  rw [hx]
  rfl
lemma scalarDistribution_mulL {a : X → ℝ} (ha : BoundedCoefficient Ω a)
    (c : Coeff) (hc : ∀ᵐ x ∂(volume.restrict Ω), eval c x=(a x : ℂ)) (f : ScalarL2 Ω) :
    scalarDistribution Ω (ha.mulL f)=c • scalarDistribution Ω f := by
  ext g
  rw [coeff_test,scalarDistribution_apply,scalarDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ha.mulL_ae f,hc] with x hx hy
  rw [hx]
  rw [ElasticityNegativeOrder.mult_apply _ (growth c),hy,Complex.ofReal_mul]
  ring
lemma stressL2_eq (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : stressL2 hl hm u i j=
      (if i=j then hl.mulL (∑ k, ambientScalar Ω (some k) k u) else 0)+
      hm.mulL (ambientScalar Ω (some j) i u+ambientScalar Ω (some i) j u) := by
  have hdiv : (∑ k, ambientScalar Ω (some k) k u : ScalarL2 Ω) =ᵐ[volume.restrict Ω]
      fun x => ∑ k, u.2 k x k := by
    have hs := lp_sum_ae Finset.univ (fun k => ambientScalar Ω (some k) k u)
    have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ k, ambientScalar Ω (some k) k u x=u.2 k x k :=
      Filter.eventually_all.mpr (fun k => ambientScalar_ae u (some k) k)
    filter_upwards [hs,he] with x hx hy
    exact hx.trans (Finset.sum_congr rfl (fun k _ => hy k))
  have hs : (ambientScalar Ω (some j) i u+ambientScalar Ω (some i) j u : ScalarL2 Ω)
      =ᵐ[volume.restrict Ω] fun x => u.2 j x i+u.2 i x j := by
    filter_upwards [Lp.coeFn_add (ambientScalar Ω (some j) i u) (ambientScalar Ω (some i) j u),
      ambientScalar_ae u (some j) i,ambientScalar_ae u (some i) j] with x hx hy hz
    exact hx.trans (congrArg₂ (·+·) hy hz)
  apply Lp.ext
  by_cases he : i=j
  · simp only [he,ite_true] at *
    filter_upwards [stressL2_ae hl hm u j j, hdiv,hs,
      hl.mulL_ae (∑ k, ambientScalar Ω (some k) k u),
      hm.mulL_ae (ambientScalar Ω (some j) j u+ambientScalar Ω (some j) j u),
      Lp.coeFn_add (hl.mulL (∑ k, ambientScalar Ω (some k) k u))
        (hm.mulL (ambientScalar Ω (some j) j u+ambientScalar Ω (some j) j u))] with x hx hd hs hl hm ha
    rw [hx,ha]
    simp only [Pi.add_apply,hl,hm,hd,hs,stressFun,ite_true]
  · simp only [he,ite_false,zero_add]
    filter_upwards [stressL2_ae hl hm u i j,hs,
      hm.mulL_ae (ambientScalar Ω (some j) i u+ambientScalar Ω (some i) j u)] with x hx hs hm
    rw [hx,hm,hs]
    simp only [stressFun,he,ite_false,zero_add]
lemma stress_distribution (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (i j : Fin 3) : scalarDistribution Ω (stressL2 hl hm u.val i j)=
    (if i=j then L • (∑ k, h1GradientDistribution u k k) else 0)+
      M • (h1GradientDistribution u i j+h1GradientDistribution u j i) := by
  rw [stressL2_eq,map_add,scalarDistribution_mulL hm M hM,map_add]
  simp only [h1GradientDistribution]
  congr 1
  split_ifs
  · rw [scalarDistribution_mulL hl L hL,map_sum]
  · exact map_zero _
/-- The physical stress of a genuine weak solution has zero distributional divergence. -/
theorem weak_stress_divergence (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u) (i : Fin 3) :
    LocalEq Ω (∑ j, dd j (scalarDistribution Ω (stressL2 hl hm u.val i j))) 0 := by
  apply localEq_of_realTest
  intro g hc hs
  simp only [sum_apply,dd_apply,lineDerivOp_apply_apply,map_neg]
  change (∑ j, -scalarDistribution Ω (stressL2 hl hm u.val i j) (∂_{coordVector j} (realTest g)))=0
  simp only [realTest_d,scalarDistribution_real,← Complex.ofReal_neg,← Complex.ofReal_sum,Finset.sum_neg_distrib]
  rw [weakSolution_stress hl hm u hu g hc hs i,neg_zero,Complex.ofReal_zero]
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma dist_sd_zero (j : Fin 3) (v : Dist) : sd (0 : Fin 3 → ℂ) j v=dd j v := by
  rw [sd_apply]
  change dd j v+(0 : ℂ) • v=dd j v
  rw [zero_smul ℂ v,add_zero]
lemma physical_gradient (u : H1 Ω) (L M : Coeff) (i : Fin 3) :
    LocalEq Ω (phys 0 L M (h1Distribution u) i)
      (dd i (L • (∑ k, h1GradientDistribution u k k))+
        ∑ j, dd j (M • (h1GradientDistribution u i j+h1GradientDistribution u j i))) := by
  simp only [phys,divd,dist_sd_zero]
  have hd : LocalEq Ω (∑ k, dd k (h1Distribution u k)) (∑ k, h1GradientDistribution u k k) :=
    LocalEq.sum Finset.univ (fun k _ => h1_distribution_derivative u k k)
  have hL := (hd.coeff L).derivative i
  have hM : ∀ j : Fin 3, LocalEq Ω
      (dd j (M • (dd j (h1Distribution u i)+dd i (h1Distribution u j))))
      (dd j (M • (h1GradientDistribution u i j+h1GradientDistribution u j i))) := by
    intro j
    exact (((h1_distribution_derivative u i j).add (h1_distribution_derivative u j i)).coeff M).derivative j
  exact hL.add (LocalEq.sum Finset.univ (fun j _ => hM j))
lemma physical_stress_sum (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (i : Fin 3) :
    (∑ j, dd j (scalarDistribution Ω (stressL2 hl hm u.val i j)))=
      dd i (L • (∑ k, h1GradientDistribution u k k))+
        ∑ j, dd j (M • (h1GradientDistribution u i j+h1GradientDistribution u j i)) := by
  simp only [stress_distribution hl hm L M hL hM,map_add,apply_ite,map_zero,Finset.sum_add_distrib]
  simp
/-- Actual weak-to-distributional physical elasticity, for the closure-defined
H1 space and its variational equation. No PDE regularity hypothesis is introduced. -/
theorem weak_physical (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u) (i : Fin 3) :
    LocalEq Ω (phys 0 L M (h1Distribution u) i) 0 := by
  have hh := physical_gradient u L M i
  rw [← physical_stress_sum hl hm L M hL hM u i] at hh
  exact hh.trans (weak_stress_divergence hl hm u hu i)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma density_full_stress (a b : ℝ) (P Q : Fin 3 → V) :
    elasticDensity a b P Q=∑ i, ∑ j,
      ((if i=j then a*(∑ k, P k k) else 0)+b*(P j i+P i j))*Q j i := by
  simp [elasticDensity,Fin.sum_univ_succ]
  ring
lemma energy_testJet_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω) (v : Ambient Ω) (hv : v∈TestJets Ω)
    (ht : ∀ (g : SchwartzMap X ℝ), HasCompactSupport (g : X → ℝ) → tsupport (g : X → ℝ)⊆Ω →
      ∀ i, (∑ j, inner ℝ (stressL2 hl hm u.val i j)
        (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0) :
    ambientEnergy lam mu u.val v=0 := by
  obtain ⟨f,hf,hd,hsm,hc,hs,hv,hvd⟩ := hv
  let F (i : Fin 3) : SchwartzMap X ℝ :=
    (hc.comp_left (g := fun y : V => y i) rfl).toSchwartzMap
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hsm)
  have he (i) := ht (F i) (hc.comp_left (g := fun y : V => y i) rfl)
    ((scalar_test_support f i).trans hs) i
  have hdv : ∀ᵐ x ∂(volume.restrict Ω), ∀ j, v.2 j x=coordDeriv f j x := by
    rw [hvd]
    exact Filter.eventually_all.mpr (fun j => (hd j).coeFn_toLp)
  have heq : ambientEnergy lam mu u.val v=∑ i, ∑ j,
      inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) (F i))) := by
    simp only [stress_pair]
    simp_rw [← integral_finsetSum _ (fun j _ => stress_pair_integrable hl hm u.val _ j _)]
    rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => stress_pair_integrable hl hm u.val i j _))]
    apply integral_congr_ae
    filter_upwards [hdv] with x hx
    simp only [ambientDensity,density_full_stress,stressFun,gradient]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hx]
    congr 1
    exact (coordDeriv_scalar f hsm i j x).symm
  rw [heq]
  simp only [he,Finset.sum_const_zero]
/-- The scalar-test stress equation is equivalent to the physical weak
formulation; the nontrivial direction uses actual density of compact test jets. -/
theorem weakSolution_of_stress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1 Ω)
    (ht : ∀ (g : SchwartzMap X ℝ), HasCompactSupport (g : X → ℝ) → tsupport (g : X → ℝ)⊆Ω →
      ∀ i, (∑ j, inner ℝ (stressL2 hl hm u.val i j)
        (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0) :
    WeakSolution Ω lam mu u := by
  let E : Ambient Ω →L[ℝ] ℝ :=
    (jetEnergy hl hm ((h1Equiv Ω).symm u).val).comp (jetEquiv Ω).symm.toContinuousLinearMap
  have hE (v : H1 Ω) : E v.val=energy Ω lam mu u v := by
    have he := jetEnergy_eq_energy hl hm ((h1Equiv Ω).symm u) ((h1Equiv Ω).symm v)
    simp only [Equiv.apply_symm_apply] at he
    change jetEnergy hl hm ((jetEquiv Ω).symm u.val) ((jetEquiv Ω).symm v.val)=_
    exact he
  have htE : MapsTo E (TestJets Ω) ({0} : Set ℝ) := by
    intro v hv
    let w : H1 Ω := ⟨v,h10Submodule_le Ω (subset_closure hv)⟩
    change E w.val=0
    rw [hE]
    exact energy_testJet_stress hl hm u v hv ht
  intro v hv
  have he := htE.closure E.continuous hv
  rw [closure_singleton] at he
  exact (hE v).symm.trans he
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
lemma schwartzH1_value (F : SchwartzMap X V) :
    (schwartzH1 (Ω := Ω) F).val.1 =ᵐ[volume.restrict Ω] (F : X → V) :=
  F.coeFn_toLp 2 (volume.restrict Ω)
lemma schwartzH1_distribution (F : SchwartzMap X V) (i : Fin 3) :
    LocalEq Ω (h1Distribution (schwartzH1 (Ω := Ω) F) i) ((realTest (componentTest F i)) : Dist) := by
  intro φ hc hs
  rw [h1Distribution,scalarDistribution_apply]
  change (∫ x, φ x * ((ambientScalar Ω none i (schwartzH1 (Ω := Ω) F).val) x : ℂ)
    ∂(volume.restrict Ω))=((realTest (componentTest F i)) : Dist) φ
  have he : ((ambientScalar Ω none i (schwartzH1 (Ω := Ω) F).val) : X → ℝ) =ᵐ[volume.restrict Ω]
      fun x => F x i := by
    filter_upwards [ambientScalar_ae (schwartzH1 (Ω := Ω) F).val none i,schwartzH1_value (Ω := Ω) F] with x hx hy
    exact hx.trans (congrArg (fun y : V => y i) hy)
  calc
    _ = ∫ x, φ x*(F x i : ℂ) ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    _ = ∫ x, φ x*(F x i : ℂ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := (φ : X → ℂ)) (fun h => hx (hs h)),zero_mul]
    _ = _ := rfl
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace ElasticityDistribution
lemma phys_add (z : Fin 3 → ℂ) (L M : Coeff) (u v : Fin 3 → Dist) (i : Fin 3) :
    phys z L M (u+v) i=phys z L M u i+phys z L M v i := by
  have ha (A : Coeff) (v w : Dist) : A • (v+w)=A • v+A • w := smul_add A v w
  simp only [phys,divd,Pi.add_apply,map_add,Finset.sum_add_distrib,ha]
  abel
lemma phys_smul (z : Fin 3 → ℂ) (L M : Coeff) (c : ℂ) (u : Fin 3 → Dist) (i : Fin 3) :
    phys z L M (c • u) i=c • phys z L M u i := by
  have hc (A : Coeff) (v : Dist) : A • (c • v)=c • (A • v) := (smul_comm c A v).symm
  have ha (v w : Dist) : c • v+c • w=c • (v+w) := (smul_add c v w).symm
  simp only [phys,divd,Pi.smul_apply,map_smul,← Finset.smul_sum,ha,hc]
end ElasticityDistribution
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma physical_realTest (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
    phys 0 L M (h1Distribution u) i (realTest g)=
      ↑(-(∑ j, inner ℝ (stressL2 hl hm u.val i j)
        (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))) := by
  have hh := physical_gradient u L M i
  rw [← physical_stress_sum hl hm L M hL hM u i] at hh
  have hgc : HasCompactSupport (realTest g : X → ℂ) := hc.comp_left (g := Complex.ofReal) rfl
  have hgs : tsupport (realTest g : X → ℂ)⊆Ω :=
    (tsupport_comp_subset (g := Complex.ofReal) rfl (g : X → ℝ)).trans hs
  rw [hh (realTest g) hgc hgs]
  simp only [sum_apply,dd_apply,lineDerivOp_apply_apply,map_neg]
  change (∑ j, -scalarDistribution Ω (stressL2 hl hm u.val i j)
    (∂_{coordVector j} (realTest g)))=_
  simp only [realTest_d,scalarDistribution_real,← Complex.ofReal_neg,← Complex.ofReal_sum,
    Finset.sum_neg_distrib]
/-- Real and imaginary parts of a physical H1 solution solve the original real
variational problems. This is derived from the actual distribution equation. -/
theorem weakSolution_parts (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ)) (u v : H1 Ω)
    (he : ∀ i, LocalEq Ω (phys 0 L M (h1Distribution u+Complex.I • h1Distribution v) i) 0) :
    WeakSolution Ω lam mu u ∧ WeakSolution Ω lam mu v := by
  have ht (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
      (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) :
      (∑ j, inner ℝ (stressL2 hl hm u.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0 ∧
      (∑ j, inner ℝ (stressL2 hl hm v.val i j) (schwartzR Ω (ElasticityKorn.d (coordVector j) g)))=0 := by
    have hgc : HasCompactSupport (realTest g : X → ℂ) := hc.comp_left (g := Complex.ofReal) rfl
    have hgs : tsupport (realTest g : X → ℂ)⊆Ω :=
      (tsupport_comp_subset (g := Complex.ofReal) rfl (g : X → ℝ)).trans hs
    have h := he i (realTest g) hgc hgs
    rw [phys_add,phys_smul] at h
    simp only [add_apply,smul_apply,smul_eq_mul,physical_realTest hl hm L M hL hM _ g hc hs i] at h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,sub_zero,add_zero] at hr
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] at hi
    exact ⟨neg_eq_zero.mp hr,neg_eq_zero.mp hi⟩
  exact ⟨weakSolution_of_stress hl hm u (fun g hc hs i => (ht g hc hs i).1),
    weakSolution_of_stress hl hm v (fun g hc hs i => (ht g hc hs i).2)⟩
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
lemma realVectorTest_apply (F : Fin 3 → SchwartzMap X ℝ) (x : X) (i : Fin 3) :
    realVectorTest F x i=F i x := by
  simp [realVectorTest,coordVector,Pi.single_apply]
lemma component_realVectorTest (F : Fin 3 → SchwartzMap X ℝ) (i : Fin 3) :
    componentTest (realVectorTest F) i=F i := by
  ext x
  exact realVectorTest_apply F x i
lemma complexH1_value (F : Fin 3 → SchwartzMap X ℂ) (i : Fin 3) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ((complexRealH1 (Ω := Ω) F).val.1 x i : ℂ)+Complex.I*((complexImagH1 (Ω := Ω) F).val.1 x i : ℂ)=F i x := by
  filter_upwards [schwartzH1_value (Ω := Ω) (realVectorTest (fun i => reTest (F i))),
    schwartzH1_value (Ω := Ω) (realVectorTest (fun i => imTest (F i)))] with x hr hi
  change ((schwartzH1 (Ω := Ω) _).val.1 x i : ℂ)+Complex.I*((schwartzH1 (Ω := Ω) _).val.1 x i : ℂ)=_
  rw [hr,hi,realVectorTest_apply,realVectorTest_apply]
  change ↑((F i x).re)+Complex.I*↑((F i x).im)=_
  exact (by rw [mul_comm]; exact Complex.re_add_im (F i x))
lemma complexH1_distribution (F : Fin 3 → SchwartzMap X ℂ) (i : Fin 3) :
    LocalEq Ω (h1Distribution (complexRealH1 (Ω := Ω) F) i+
      Complex.I • h1Distribution (complexImagH1 (Ω := Ω) F) i) ((F i) : Dist) := by
  have hr := schwartzH1_distribution (Ω := Ω) (realVectorTest (fun i => reTest (F i))) i
  have hi := schwartzH1_distribution (Ω := Ω) (realVectorTest (fun i => imTest (F i))) i
  rw [component_realVectorTest] at hr hi
  have he := hr.add (hi.smul Complex.I)
  rw [← coe_schwartz_smul,← coe_schwartz_add,
    ← test_parts (F i)] at he
  exact he
lemma localEq_of_schwartz_eqOn {F G : SchwartzMap X ℂ} (h : Set.EqOn (F : X → ℂ) G Ω) :
    LocalEq Ω (F : Dist) (G : Dist) := by
  intro φ _ hs
  change (∫ x, φ x*F x)=(∫ x, φ x*G x)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change φ x*F x=φ x*G x
    by_cases hx : x∈Ω
    · rw [h hx]
    · rw [image_eq_zero_of_notMem_tsupport (f := (φ : X → ℂ)) (fun hg => hx (hs hg)),zero_mul,zero_mul])
/-- A classical complex physical field embeds into the literal real DN problem
through its two actual H1 parts, rather than a presumed complex boundary map. -/
theorem complexH1_weak {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M : Coeff) (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ)) (F : Fin 3 → SchwartzMap X ℂ)
    (he : ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L) (eval M) F i : X → ℂ) 0 Ω) :
    WeakSolution Ω lam mu (complexRealH1 (Ω := Ω) F) ∧
      WeakSolution Ω lam mu (complexImagH1 (Ω := Ω) F) := by
  apply weakSolution_parts hl hm L M hL hM
  intro i
  have hp := LocalEq.physical (complexH1_distribution (Ω := Ω) F) 0 L M i
  rw [phys_schwartz] at hp
  have hh := localEq_of_schwartz_eqOn (F := ElasticityPhysicalAlgebra.physical 0 (eval L) (eval M) F i)
    (G := 0) (he i)
  simpa only [map_zero,Pi.add_def,Pi.smul_def] using hp.trans hh
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set TemperedDistribution
open scoped BigOperators SchwartzMap
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
lemma scalarGlobal_ae (hs : MeasurableSet Ω) (f : ScalarL2 Ω) :
    (scalarGlobal hs f : X → ℂ)=ᵐ[volume] Ω.indicator (fun x => (f x : ℂ)) := by
  filter_upwards [lpZeroExtend_coe volume Ω hs (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f),
    (ae_restrict_iff' hs).mp (ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f)] with x hx hy
  rw [scalarGlobal,hx]
  by_cases he : x∈Ω
  · simp only [indicator_of_mem he,hy he]
    rfl
  · simp only [indicator_of_notMem he]
lemma scalarGlobal_distribution (hs : MeasurableSet Ω) (f : ScalarL2 Ω) :
    (scalarGlobal hs f : Dist)=scalarDistribution Ω f := by
  ext g
  rw [Lp.toTemperedDistribution_apply,scalarDistribution_apply]
  calc
    _ = ∫ x, Ω.indicator (fun y => g y*(f y : ℂ)) x ∂volume := by
      apply integral_congr_ae
      filter_upwards [scalarGlobal_ae hs f] with x hx
      rw [hx]
      by_cases he : x∈Ω
      · simp only [indicator_of_mem he,smul_eq_mul]
      · simp only [indicator_of_notMem he,smul_zero]
    _ = _ := integral_indicator hs
lemma h1Global_distribution (hs : MeasurableSet Ω) (u : H1 Ω) (i : Fin 3) :
    (h1Global hs u i : Dist)=h1Distribution u i := scalarGlobal_distribution hs _
lemma h1Global_ae (hs : MeasurableSet Ω) (u : H1 Ω) (i : Fin 3) :
    ∀ᵐ x ∂volume, x∈Ω → h1Global hs u i x=(u.val.1 x i : ℂ) := by
  filter_upwards [scalarGlobal_ae hs (ambientScalar Ω none i u.val),
    (ae_restrict_iff' hs).mp (ambientScalar_ae u.val none i)] with x hx hy
  intro he
  change scalarGlobal hs (ambientScalar Ω none i u.val) x=_
  rw [hx,indicator_of_mem he,hy he]
  rfl
/-- Interior regularization now applies to the genuine variational solution,
not a hypothetical distribution satisfying an assumed physical equation. -/
theorem h1_classical_representative (hΩ : IsOpen Ω) {Ω' : Set X} (hΩ' : IsOpen Ω') (hsub : Ω'⊆Ω)
    (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (L M N O : Coeff) (hN : N*M=1) (hO : O*(L+M+M)=1)
    (hL : ∀ᵐ x ∂(volume.restrict Ω), eval L x=(lam x : ℂ))
    (hM : ∀ᵐ x ∂(volume.restrict Ω), eval M x=(mu x : ℂ))
    (u : H1 Ω) (hu : WeakSolution Ω lam mu u)
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Ω) (h1 : Set.EqOn g 1 Ω') :
    ∃ v : Fin 3 → SchwartzMap X ℂ,
      (∀ i, ∀ᵐ x ∂volume, x∈Ω' → (u.val.1 x i : ℂ)=v i x) ∧
      ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L) (eval M) v i : X → ℂ) 0 Ω' := by
  have he : ∀ i, LocalEq Ω (phys 0 L M (fun j => (h1Global hΩ.measurableSet u j : Dist)) i)
      ((0 : SchwartzMap X ℂ) : Dist) := by
    intro i
    simp only [h1Global_distribution,map_zero]
    exact weak_physical hl hm L M hL hM u hu i
  obtain ⟨v,hv,hve⟩ := classical_representative hΩ' hsub 0 L M N O hN hO
    (h1Global hΩ.measurableSet u) (fun _ => 0) he hg hc hs h1
  refine ⟨v,fun i => ?_,hve⟩
  filter_upwards [hv i,h1Global_ae hΩ.measurableSet u i] with x hx hy
  intro he
  exact (hy (hsub he)).symm.trans (hx he)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω B B' : Set X} {lam₁ mu₁ lam₂ mu₂ : X → ℝ}
/-- Actual smooth complex physical transfer on an interior ball, from the
original real variational DN equality. No augmented/artificial DN map is used. -/
theorem physical_classical_transfer_oai
    (ha₁ : Admissible Ω lam₁ mu₁) (ha₂ : Admissible Ω lam₂ mu₂)
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hΩB : Ω⊆B)
    (hB : IsOpen B) (hB' : IsOpen B') (hsub : B'⊆B)
    (hl₁ : BoundedCoefficient B lam₁) (hm₁ : BoundedCoefficient B mu₁)
    (hl₂ : BoundedCoefficient B lam₂) (hm₂ : BoundedCoefficient B mu₂)
    (he : ∀ x∉Ω, lam₁ x=lam₂ x ∧ mu₁ x=mu₂ x)
    (hDN : DN Ω lam₁ mu₁=DN Ω lam₂ mu₂)
    (L₁ M₁ L₂ M₂ N₂ O₂ : Coeff) (hN : N₂*M₂=1) (hO : O₂*(L₂+M₂+M₂)=1)
    (hL₁ : ∀ᵐ x ∂(volume.restrict B), eval L₁ x=(lam₁ x : ℂ))
    (hM₁ : ∀ᵐ x ∂(volume.restrict B), eval M₁ x=(mu₁ x : ℂ))
    (hL₂ : ∀ᵐ x ∂(volume.restrict B), eval L₂ x=(lam₂ x : ℂ))
    (hM₂ : ∀ᵐ x ∂(volume.restrict B), eval M₂ x=(mu₂ x : ℂ))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : Set.EqOn g 1 B') (F : Fin 3 → SchwartzMap X ℂ)
    (hF : ∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₁) (eval M₁) F i : X → ℂ) 0 B) :
    ∃ G : Fin 3 → SchwartzMap X ℂ,
      (∀ i, Set.EqOn (ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) G i : X → ℂ) 0 B') ∧
      ∀ i, Set.EqOn (G i : X → ℂ) (F i) (B'\closure Ω) := by
  obtain ⟨hr,hi⟩ := complexH1_weak hl₁ hm₁ L₁ M₁ hL₁ hM₁ F hF
  obtain ⟨wr,hwr,hre,_⟩ := physical_weak_transfer ha₁ ha₂ hΩ hOB hΩB hl₁ hm₁ hl₂ hm₂ he hDN hr
  obtain ⟨wi,hwi,hie,_⟩ := physical_weak_transfer ha₁ ha₂ hΩ hOB hΩB hl₁ hm₁ hl₂ hm₂ he hDN hi
  obtain ⟨R,hR,hRp⟩ := h1_classical_representative hB hB' hsub hl₂ hm₂ L₂ M₂ N₂ O₂ hN hO hL₂ hM₂ wr hwr hg hc hs h1
  obtain ⟨I,hI,hIp⟩ := h1_classical_representative hB hB' hsub hl₂ hm₂ L₂ M₂ N₂ O₂ hN hO hL₂ hM₂ wi hwi hg hc hs h1
  let G : Fin 3 → SchwartzMap X ℂ := R+Complex.I • I
  refine ⟨G,?_,?_⟩
  · intro i x hx
    change ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) (R+Complex.I • I) i x=0
    rw [ElasticityPhysicalDual.physical_add,ElasticityPhysicalDual.physical_smul]
    change ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) R i x+
      Complex.I*ElasticityPhysicalAlgebra.physical 0 (eval L₂) (eval M₂) I i x=0
    simp only [hRp i hx,hIp i hx,Pi.zero_apply,mul_zero,add_zero]
  · intro i
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure X)) _ (hB'.sdiff isClosed_closure)
      (G i).continuous.continuousOn (F i).continuous.continuousOn
    apply (ae_restrict_iff' (hB'.measurableSet.diff isClosed_closure.measurableSet)).mpr
    have hre' := (ae_restrict_iff' hB.measurableSet).mp hre
    have hie' := (ae_restrict_iff' hB.measurableSet).mp hie
    have hFv := (ae_restrict_iff' hB.measurableSet).mp (complexH1_value (Ω := B) F i)
    filter_upwards [hR i,hI i,hre',hie',hFv] with x hRx hIx hrx hix hFx hx
    have hxB := hsub hx.1
    have hxo : x∉Ω := fun hh => hx.2 (subset_closure hh)
    change R i x+Complex.I*I i x=F i x
    rw [← hRx hx.1,← hIx hx.1,hrx hxB hxo,hix hxB hxo]
    exact hFx hxB
end Elasticity

end
end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.physical_classical_transfer_oai := @OAI.Elasticity.physical_classical_transfer_oai
