-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:11:32.474565+00:00
-- url     : https://prove2.me/submissions/e7964aa1-95e1-444a-9b88-9438a33936d3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B176

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelMixtureControl
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem fixedKernelMixture_difference_le {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (g f h : T → ℝ) (hg : Integrable g μ) (hg0 : ∀ t, 0 ≤ g t)
    (hgmass : (∫ t, g t ∂μ) = 1)
    (hf : Integrable (fun t => g t * f t) μ) (hh : Integrable (fun t => g t * h t) μ)
    {E : ℝ} (he : ∀ t, g t ≠ 0 → |f t-h t| ≤ E) :
    |(∫ t, g t * f t ∂μ) - ∫ t, g t * h t ∂μ| ≤ E := by
  rw [← integral_sub hf hh]
  have hb (t) : ‖g t * f t-g t * h t‖ ≤ g t * E := by
    by_cases ht : g t = 0
    · simp only [ht, zero_mul, sub_self, norm_zero, le_refl]
    · rw [← mul_sub, norm_mul, Real.norm_of_nonneg (hg0 t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (he t ht) (hg0 t)
  have hi := norm_integral_le_of_norm_le (hg.mul_const E) (Filter.Eventually.of_forall hb)
  simpa only [Real.norm_eq_abs, integral_mul_const, hgmass, one_mul] using hi

theorem fixedKernelMixture_abs_le {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (g f : T → ℝ) (hg : Integrable g μ) (hg0 : ∀ t, 0 ≤ g t)
    (hgmass : (∫ t, g t ∂μ) = 1) {H : ℝ}
    (hb : ∀ t, g t ≠ 0 → |f t| ≤ H) : |∫ t, g t * f t ∂μ| ≤ H := by
  have hpoint (t) : ‖g t * f t‖ ≤ g t * H := by
    by_cases ht : g t = 0
    · simp only [ht, zero_mul, norm_zero, le_refl]
    · rw [norm_mul, Real.norm_of_nonneg (hg0 t), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb t ht) (hg0 t)
  have hi := norm_integral_le_of_norm_le (hg.mul_const H) (Filter.Eventually.of_forall hpoint)
  simpa only [Real.norm_eq_abs, integral_mul_const, hgmass, one_mul] using hi

theorem fixedKernelMixture_lipschitzOn {X T : Type*} [PseudoMetricSpace X] [MeasurableSpace T]
    (μ : Measure T) (g : T → ℝ) (F : X → T → ℝ) (S : Set X) (L : ℝ≥0)
    (hg : Integrable g μ) (hg0 : ∀ t, 0 ≤ g t) (hgmass : (∫ t, g t ∂μ) = 1)
    (hint : ∀ x ∈ S, Integrable (fun t => g t * F x t) μ)
    (hLip : ∀ t, g t ≠ 0 → LipschitzOnWith L (fun x => F x t) S) :
    LipschitzOnWith L (fun x => ∫ t, g t * F x t ∂μ) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  exact fixedKernelMixture_difference_le μ g (F x) (F y) hg hg0 hgmass (hint x hx) (hint y hy)
    (fun t ht => (hLip t ht).dist_le_mul x hx y hy)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem pivotOutputDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, f (y, A.symm (v - B y)) := by
  exact integral_const_mul _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_zero_outside (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {R : ℝ}
    (hf : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) (y : J → ℝ) (hy : R < ‖y‖) :
    pivotSliceProfile A B f v y = 0 :=
  hf _ (hy.trans_le (norm_fst_le (y, A.symm (v - B y))))

theorem pivotSliceProfile_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    (hf : Continuous f) {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (v : I → ℝ) :
    Integrable (pivotSliceProfile A B f v) := by
  have hc : Continuous (pivotSliceProfile A B f v) := by
    unfold pivotSliceProfile
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : J → ℝ) R)
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  exact hy (pivotSliceProfile_zero_outside A B hsupport v y h)

omit [Fintype I] in
theorem pivotOutputDensity_slice_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℝ) :
    pivotOutputDensity A B f v = inverseJacobian A * ∫ y, pivotSliceProfile A B f v y :=
  pivotOutputDensity_formula A B f v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem splitInputProfile_integral (f : (J → ℝ) × (I → ℝ) → ℝ) :
    (∫ x, splitInputProfile f x) = ∫ p, f p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).integral_comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℝ)).measurableEmbedding f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomialMonomial_mass_le {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) {M : ℝ}
    (ha : ∀ k ∈ m.support, realPolynomialMass (a k) ≤ M) :
    realPolynomialMass (polynomialMonomial a m) ≤ M ^ (m.sum fun _ n => n) := by
  classical
  apply (realPolynomialMass_prod_le _ _).trans
  calc
    _ ≤ ∏ k ∈ m.support, M ^ m k := by
      apply Finset.prod_le_prod (fun _ _ => realPolynomialMass_nonneg _)
      intro k hk
      exact (realPolynomialMass_pow_le _ _).trans
        (pow_le_pow_left₀ (realPolynomialMass_nonneg _) (ha k hk) _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]; rfl

theorem polynomialMonomial_totalDegree_le {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) {e : ℕ}
    (ha : ∀ k ∈ m.support, (a k).totalDegree ≤ e) :
    (polynomialMonomial a m).totalDegree ≤ (m.sum fun _ n => n) * e := by
  classical
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ k ∈ m.support, m k * e := Finset.sum_le_sum (fun k hk =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (ha k hk)))
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.OperatorCoordinateBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem clm_norm_le_card_mul_of_entries {I O : Type*}
    [Fintype I] [DecidableEq I] [Fintype O]
    (A : (I → ℝ) →L[ℝ] (O → ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i o, |A (Pi.single i 1) o| ≤ M) : ‖A‖ ≤ Fintype.card I * M := by
  apply clm_norm_le_card_mul_of_basis A hM
  intro i
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro o
  simpa only [Real.norm_eq_abs] using hA i o

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanFeature_abs_le_one {α : Type*} [DecidableEq α]
    (r : Option α) (t : Finset α) : |(booleanFeature r t : ℝ)| ≤ 1 := by
  cases r with
  | none => norm_num [booleanFeature]
  | some a => simp only [booleanFeature]; split_ifs <;> norm_num

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mvPolynomial_support_card_le_fintype {I : Type*} [Fintype I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d) :
    p.support.card ≤ (d + 1) ^ Fintype.card I := by
  classical
  let f : p.support → (I → Fin (d + 1)) := fun m i =>
    ⟨m.val i, Nat.lt_succ_of_le ((MvPolynomial.degreeOf_le_iff.mp (hd i)) m.val m.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hab i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem mvPolynomial_unit_box_bound {I : Type*} [Fintype I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x p| ≤ (d + 1 : ℝ) ^ Fintype.card I * C := by
  have hcard : (p.support.card : ℝ) ≤ (d + 1 : ℝ) ^ Fintype.card I := by
    exact_mod_cast mvPolynomial_support_card_le_fintype p hd
  calc
    _ ≤ ∑ m ∈ p.support, |p.coeff m| := mvPolynomial_eval_abs_le_sum_coeff p x hx
    _ ≤ ∑ _m ∈ p.support, C := Finset.sum_le_sum (fun m _ => hc m)
    _ = (p.support.card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hC

theorem mvPolynomial_pderiv_coeff_bound {I : Type*} [DecidableEq I]
    (p : MvPolynomial I ℝ) (j : I) {d : ℕ} (hd : p.degreeOf j ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C) (m : I →₀ ℕ) :
    |(MvPolynomial.pderiv j p).coeff m| ≤ (d : ℝ) * C := by
  rw [MvPolynomial.coeff_pderiv]
  by_cases hz : p.coeff (m + Finsupp.single j 1) = 0
  · rw [hz, zero_mul, abs_zero]
    positivity
  · have hd' := MvPolynomial.degreeOf_le_iff.mp hd _ (MvPolynomial.mem_support_iff.mpr hz)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hd'
    have hdR : (m j + 1 : ℝ) ≤ d := by exact_mod_cast hd'
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ m j + 1)]
    exact (mul_le_mul (hc _) hdR (by positivity) hC).trans_eq (mul_comm C d)

theorem mvPolynomial_pderiv_unit_box_bound {I : Type*} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) {d : ℕ} (hd : ∀ i, p.degreeOf i ≤ d)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ m, |p.coeff m| ≤ C)
    (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) (j : I) :
    |MvPolynomial.eval x (MvPolynomial.pderiv j p)| ≤
      (d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * C) :=
  mvPolynomial_unit_box_bound _ (fun i => mvPolynomial_pderiv_degreeOf_le p j i (hd i))
    (by positivity) (mvPolynomial_pderiv_coeff_bound p j (hd j) hC hc) x hx

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]

omit [DecidableEq I] in
theorem polynomialVectorMap_contDiff (p : O → MvPolynomial I ℝ) :
    ContDiff ℝ ∞ (polynomialVectorMap p) := contDiff_pi.mpr (fun o => mvPolynomial_contDiff_eval (p o))

theorem polynomialVectorMap_fderiv_entry (p : O → MvPolynomial I ℝ) (x : I → ℝ) (i : I) (o : O) :
    fderiv ℝ (polynomialVectorMap p) x (Pi.single i 1) o =
      MvPolynomial.eval x (MvPolynomial.pderiv i (p o)) := by
  have hd := (polynomialVectorMap_contDiff p).differentiable (by norm_num) x
  have he := mvPolynomial_fderiv_coordinate (p o) x i
  change fderiv ℝ (fun y => polynomialVectorMap p y o) x (Pi.single i 1) = _ at he
  rw [fderiv_apply hd o] at he
  exact he

theorem polynomialVectorMap_fderiv_bound (p : O → MvPolynomial I ℝ) {d : ℕ}
    (hd : ∀ o i, (p o).degreeOf i ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ o m, |(p o).coeff m| ≤ C) (x : I → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤
      Fintype.card I * ((d + 1 : ℝ) ^ Fintype.card I * ((d : ℝ) * C)) := by
  apply clm_norm_le_card_mul_of_entries _ (by positivity)
  intro i o
  rw [polynomialVectorMap_fderiv_entry]
  exact mvPolynomial_pderiv_unit_box_bound (p o) (hd o) hC (hc o) x hx i

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem polynomialVectorMap_lipschitzOn_box {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (p : O → MvPolynomial I ℝ) {d : ℕ} (hd : ∀ o, (p o).totalDegree ≤ d)
    (C : ℝ≥0) (hc : ∀ o, realPolynomialMass (p o) ≤ C) :
    LipschitzOnWith (polynomialBoxLip (Fintype.card I) d C) (polynomialVectorMap p)
      (Metric.closedBall 0 1) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (polynomialVectorMap_contDiff p).differentiable (by norm_num) x) _ (convex_closedBall 0 1)
  intro x hx
  have hx' : ∀ i, |x i| ≤ 1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    intro i
    exact (norm_le_pi_norm x i).trans hx
  have he := polynomialVectorMap_fderiv_bound p
    (fun o i => (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hd o)) C.coe_nonneg
    (fun o m => (realPolynomialMass_coeff_le (p o) m).trans (hc o)) x hx'
  change ‖fderiv ℝ (polynomialVectorMap p) x‖ ≤ (polynomialBoxLip (Fintype.card I) d C : ℝ)
  simpa only [polynomialBoxLip, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast,
    NNReal.coe_add, NNReal.coe_one] using he

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem matrixSupCLM_sub {I J : Type*} [Fintype I] [Fintype J] (A B : Matrix I J ℝ) :
    matrixSupCLM (A-B) = matrixSupCLM A-matrixSupCLM B := by
  ext x i
  exact congrFun (Matrix.sub_mulVec A B x) i

theorem polynomialColumns_lipschitzOn_box {P I J : Type*} [Fintype P] [DecidableEq P]
    [Fintype I] [Fintype J] (p : I → J → MvPolynomial P ℝ) {d : ℕ}
    (hd : ∀ i j, (p i j).totalDegree ≤ d) (C : ℝ≥0) (hc : ∀ i j, realPolynomialMass (p i j) ≤ C) :
    LipschitzOnWith (Fintype.card J * polynomialBoxLip (Fintype.card P) d C)
      (polynomialColumns p) (Metric.closedBall 0 1) := by
  have hp := polynomialVectorMap_lipschitzOn_box (fun ij : I × J => p ij.1 ij.2)
    (fun ij => hd ij.1 ij.2) C (fun ij => hc ij.1 ij.2)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hE : 0 ≤ (polynomialBoxLip (Fintype.card P) d C : ℝ)*dist x y := by positivity
  have he (i) (j) : |MvPolynomial.eval x (p i j)-MvPolynomial.eval y (p i j)| ≤
      (polynomialBoxLip (Fintype.card P) d C : ℝ)*dist x y :=
    (dist_le_pi_dist (polynomialVectorMap (fun ij : I × J => p ij.1 ij.2) x)
      (polynomialVectorMap (fun ij : I × J => p ij.1 ij.2) y) (i,j)).trans (hp.dist_le_mul x hx y hy)
  let A : Matrix I J ℝ := fun i j => MvPolynomial.eval x (p i j)
  let B : Matrix I J ℝ := fun i j => MvPolynomial.eval y (p i j)
  rw [dist_eq_norm]
  change ‖matrixSupCLM A-matrixSupCLM B‖ ≤ _
  rw [← matrixSupCLM_sub]
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_assoc] using
    matrixSupCLM_norm_le (A-B) hE he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanPolynomialBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_mass_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {M : ℝ}
    (hp : ∀ t ∈ s.powerset, realPolynomialMass (p t) ≤ M) :
    realPolynomialMass (booleanCoefficient p s) ≤ (2 : ℝ) ^ s.card * M := by
  classical
  unfold booleanCoefficient
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _t ∈ s.powerset, M := by
      apply Finset.sum_le_sum
      intro t ht
      have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
          MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
      rw [he]
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa using hp t ht)
    _ = _ := by simp

theorem booleanCoefficient_totalDegree_le {I α : Type*} [DecidableEq α]
    (p : Finset α → MvPolynomial I ℝ) (s : Finset α) {d : ℕ}
    (hp : ∀ t ∈ s.powerset, (p t).totalDegree ≤ d) :
    (booleanCoefficient p s).totalDegree ≤ d := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t ht
  have he : (-1 : MvPolynomial I ℝ) ^ (s \ t).card =
      MvPolynomial.C ((-1 : ℝ) ^ (s \ t).card) := by simp
  rw [he]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using hp t ht)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BooleanAffineInput
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanAffineInput_mass_le {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) {A : ℝ}
    (ha : ∀ r, realPolynomialMass (a r) ≤ A) :
    realPolynomialMass (booleanAffineInput a t) ≤ ((Fintype.card α : ℝ) + 1) * A := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _r : Option α, A := by
      apply Finset.sum_le_sum
      intro r _
      apply (realPolynomialMass_C_mul_le _ _).trans
      simpa only [one_mul] using mul_le_mul (booleanFeature_abs_le_one r t)
        (ha r) (realPolynomialMass_nonneg _) zero_le_one
    _ = _ := by simp

theorem booleanAffineInput_totalDegree_le {I α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → MvPolynomial I ℝ) (t : Finset α) {e : ℕ}
    (ha : ∀ r, (a r).totalDegree ≤ e) : (booleanAffineInput a t).totalDegree ≤ e := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [MvPolynomial.totalDegree_C, zero_add] using ha r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanJetColumnPolynomial_mass_le {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α)
    {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) {A : ℝ}
    (hA : 1 ≤ ((Fintype.card α : ℝ)+1)*A) (hi : ∀ k r, realPolynomialMass (input k r) ≤ A) :
    realPolynomialMass (booleanJetColumnPolynomial e input s) ≤
      2^s.card * (((Fintype.card α : ℝ)+1)*A)^d := by
  apply booleanCoefficient_mass_le
  intro t _
  exact (polynomialMonomial_mass_le _ _ (fun k _ => booleanAffineInput_mass_le _ _ (hi k))).trans
    (pow_le_pow_right₀ hA hd)

theorem booleanJetColumnPolynomial_degree_le {K P α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → MvPolynomial P ℝ) (s : Finset α)
    {d a : ℕ} (hd : e.sum (fun _ n => n) ≤ d) (hi : ∀ k r, (input k r).totalDegree ≤ a) :
    (booleanJetColumnPolynomial e input s).totalDegree ≤ d*a := by
  apply booleanCoefficient_totalDegree_le
  intro t _
  exact (polynomialMonomial_totalDegree_le _ _ (fun k _ => booleanAffineInput_totalDegree_le _ _ (hi k))).trans
    (Nat.mul_le_mul_right a hd)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensityCap
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotOutputDensity_abs_le (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {R H : ℝ} (hR : 0 ≤ R) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hbound : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    |pivotOutputDensity A B f v| ≤ inverseJacobian A * H * (2 * R) ^ Fintype.card J := by
  have hi := integral_norm_le_box (pivotSliceProfile A B f v) hR
    (pivotSliceProfile_zero_outside A B hsupport v) (fun y _ => hbound _)
  have hb := (norm_integral_le_integral_norm (f := pivotSliceProfile A B f v)).trans hi
  rw [pivotOutputDensity_slice_formula, abs_mul, abs_of_pos (inverseJacobian_pos A)]
  have h := mul_le_mul_of_nonneg_left hb (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs, mul_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitFreeProfile_slice_integrable (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    Integrable (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by
  have hc : Continuous (fun p : (J → ℝ) × (N → ℝ) =>
      f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : (J → ℝ) × (N → ℝ)) (max R S))
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! h
  apply hp
  have heq : ‖Sum.elim p.1 p.2‖ = ‖p‖ := (splitCoordinates_norm (Sum.elim p.1 p.2)).symm
  have hz := splitFreeProfile_zero_outside hfs hgs
    (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))
    (h.trans_le (heq ▸ norm_fst_le
      (Sum.elim p.1 p.2, A.symm (v - (B p.1 + C p.2)))))
  exact hz

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedCoefficientProfile_norm_le {I J : Type*} [Fintype I]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {H : ℝ} (hf : ∀ x, ‖f x‖ ≤ H) :
    ∀ p, ‖selectedCoefficientProfile s f p‖ ≤ H := fun p => hf (selectedCoefficientEquiv s ℝ p)

theorem selectedCoefficientProfile_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {f : (J → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (selectedCoefficientProfile s f) := by
  simpa only [mul_one, selectedCoefficientProfile] using hf.comp (selectedCoefficientEquiv_lipschitz s)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ScalarCubeProductSupport
namespace OAI


namespace Erdos3

open MeasureTheory

theorem integerScalarCubeBox_normalized_norm_le {I : Type*} [Fintype I] {L : ℕ}
    (hL : 0 < L) (z : IntegerScalarCubeBox I L) : ‖fun i => (z i : ℝ) / L‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  have hz := Finset.mem_Ico.mp (z i).property
  have hbound : |(z i : ℝ)| ≤ L := abs_le.mpr
    ⟨by exact_mod_cast hz.1, by exact_mod_cast hz.2.le⟩
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by exact_mod_cast hL : (0 : ℝ) < L)]
  exact (div_le_one (by exact_mod_cast hL)).mpr hbound

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedJetColumns
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem frozenTupleCoordinate_mass_le {Z P : Type*} (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (i : Z ⊕ P) :
    realPolynomialMass (frozenTupleCoordinate z i) ≤ 1 := by
  cases i with
  | inl j => exact (realPolynomialMass_C (z j)).le.trans (hz j)
  | inr i => exact (realPolynomialMass_X i).le

theorem frozenTupleCoordinate_degree_le {Z P : Type*} (z : Z → ℝ) (i : Z ⊕ P) :
    (frozenTupleCoordinate z i).totalDegree ≤ 1 := by
  cases i <;> simp [frozenTupleCoordinate]

theorem normalizedJetColumn_degree_le {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (s : Finset α)
    {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) : (normalizedJetColumn e input z s).totalDegree ≤ d := by
  simpa only [normalizedJetColumn, Nat.mul_one] using booleanJetColumnPolynomial_degree_le e _ s hd
    (fun k r => frozenTupleCoordinate_degree_le z (input k r))

theorem normalizedJetColumn_mass_le {Z P K α : Type*} [Fintype α] [DecidableEq α]
    (e : K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (s : Finset α) {d : ℕ} (hd : e.sum (fun _ n => n) ≤ d) :
    realPolynomialMass (normalizedJetColumn e input z s) ≤
      (2 : ℝ)^Fintype.card α * ((Fintype.card α : ℝ)+1)^d := by
  have he := booleanJetColumnPolynomial_mass_le e _ s hd (A := 1) (by simp)
    (fun k r => frozenTupleCoordinate_mass_le z hz (input k r))
  simp only [mul_one] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.card_le_univ s)) (by positivity))

theorem normalizedJetColumns_lipschitzOn_box {Z P K α O J : Type*}
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] [Fintype O] [Fintype J]
    (e : J → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : O → Finset α) {d : ℕ} (hd : ∀ j, (e j).sum (fun _ n => n) ≤ d) :
    LipschitzOnWith (Fintype.card J * polynomialBoxLip (Fintype.card P) d (normalizedJetMass α d))
      (polynomialColumns (fun o j => normalizedJetColumn (e j) input z (rows o))) (Metric.closedBall 0 1) := by
  apply polynomialColumns_lipschitzOn_box _ (fun o j => normalizedJetColumn_degree_le (e j) input z (rows o) (hd j))
  intro o j
  change realPolynomialMass (normalizedJetColumn (e j) input z (rows o)) ≤
    (2 : ℝ)^Fintype.card α * (Fintype.card α+1)^d
  exact normalizedJetColumn_mass_le (e j) input z hz (rows o) (hd j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotOutputLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

theorem pivotSliceProfile_output_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (v w : I → ℝ) (y : J → ℝ) :
    ‖pivotSliceProfile A B f v y - pivotSliceProfile A B f w y‖ ≤
      K * ‖A.symm.toContinuousLinearMap‖ * ‖v - w‖ := by
  have h := hf.norm_sub_le (y, A.symm (v - B y)) (y, A.symm (w - B y))
  have heq : (y, A.symm (v - B y)) - (y, A.symm (w - B y)) =
      ((0 : J → ℝ), A.symm (v - w)) := by
    ext i <;> simp [← map_sub]
  rw [heq, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h
  exact h.trans (by
    simpa only [ContinuousLinearEquiv.coe_coe, mul_assoc] using mul_le_mul_of_nonneg_left
      (A.symm.toContinuousLinearMap.le_opNorm (v - w)) K.coe_nonneg)

theorem pivotOutputDensity_output_bound (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) (v w : I → ℝ) :
    |pivotOutputDensity A B f v - pivotOutputDensity A B f w| ≤
      (inverseJacobian A * (2 * R) ^ Fintype.card J * K *
        ‖A.symm.toContinuousLinearMap‖) * ‖v - w‖ := by
  have hi (u) := pivotSliceProfile_integrable A B hf.continuous hsupport u
  have hb := integral_norm_le_box
    (fun y => pivotSliceProfile A B f v y - pivotSliceProfile A B f w y) hR
    (fun y hy => by rw [pivotSliceProfile_zero_outside A B hsupport v y hy,
      pivotSliceProfile_zero_outside A B hsupport w y hy, sub_self])
    (fun y _ => pivotSliceProfile_output_bound A B hf v w y)
  rw [pivotOutputDensity_slice_formula, pivotOutputDensity_slice_formula,
    ← mul_sub, ← integral_sub (hi v) (hi w), abs_mul,
    abs_of_pos (inverseJacobian_pos A)]
  have hn := (norm_integral_le_integral_norm
    (f := fun y => pivotSliceProfile A B f v y - pivotSliceProfile A B f w y)).trans hb
  have hm := mul_le_mul_of_nonneg_left hn (inverseJacobian_pos A).le
  simpa only [Real.norm_eq_abs] using hm.trans_eq (by ring)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotKernelAllowances
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem pivotOutputDensity_norm_le_cap {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (f : (J → ℝ) × (I → ℝ) → ℝ) (R H : ℝ≥0)
    (hs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hb : ∀ p, ‖f p‖ ≤ H) (v : I → ℝ) :
    ‖pivotOutputDensity A B f v‖ ≤ pivotKernelCap J A R H := by
  change ‖pivotOutputDensity A B f v‖ ≤ inverseJacobian A * (H : ℝ) * (2*(R : ℝ))^Fintype.card J
  exact pivotOutputDensity_abs_le A B f R.coe_nonneg hs hb v

theorem pivotOutputDensity_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} (R K : ℝ≥0) (hf : LipschitzWith K f)
    (hs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) :
    LipschitzWith (pivotKernelLip J A R K) (pivotOutputDensity A B f) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, dist_eq_norm]
  apply (pivotOutputDensity_output_bound A B hf R.coe_nonneg hs v w).trans_eq
  change _ = (inverseJacobian A * (K : ℝ) * (2*(R : ℝ))^Fintype.card J *
    ‖A.symm.toContinuousLinearMap‖) * ‖v-w‖
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PivotDensitySupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]

theorem splitPivotDensity_formula (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (C : (N → ℝ) →L[ℝ] (I → ℝ))
    {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : Continuous f) (hg : Continuous g) {R S : ℝ}
    (hfs : ∀ p, R < ‖p‖ → f p = 0) (hgs : ∀ n, S < ‖n‖ → g n = 0)
    (v : I → ℝ) :
    pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v =
      ∫ n, g n * pivotOutputDensity A B f (v - C n) := by
  let F : (J → ℝ) × (N → ℝ) → ℝ := fun p =>
    f (p.1, A.symm (v - (B p.1 + C p.2))) * g p.2
  have hi : Integrable F := splitFreeProfile_slice_integrable A B C hf hg hfs hgs v
  rw [pivotOutputDensity_formula]
  change inverseJacobian A * (∫ y, splitInputProfile F y) = _
  rw [splitInputProfile_integral, Measure.volume_eq_prod, integral_prod_symm _ hi,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  have heq (y : J → ℝ) : v - (B y + C n) = (v - C n) - B y := by abel
  simp only [F, heq, integral_mul_const, pivotOutputDensity_formula]
  ring

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitPivotParameter
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem splitPivotDensity_norm_le_cap {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : (N → ℝ) →L[ℝ] (I → ℝ)) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (R H S : ℝ≥0) (hf : Continuous f) (hg : Continuous g)
    (hfs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ p, ‖f p‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1)
    (v : I → ℝ) :
    ‖pivotOutputDensity A (splitFreeColumns B C) (splitFreeProfile f g) v‖ ≤ pivotKernelCap J A R H := by
  rw [Real.norm_eq_abs, splitPivotDensity_formula A B C hf hg hfs hgs v]
  exact fixedKernelMixture_abs_le volume g _ (compactBox_integrable g hg S hgs) hg0 hgmass
    (fun n _ => pivotOutputDensity_norm_le_cap A B f R H hfs hfb (v-C n))

theorem splitPivotDensity_parameter_lipschitzOn {X I J N : Type*} [PseudoMetricSpace X]
    [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (B : (J → ℝ) →L[ℝ] (I → ℝ))
    (C : X → (N → ℝ) →L[ℝ] (I → ℝ)) (T : Set X) (L R K S : ℝ≥0)
    (hC : LipschitzOnWith L C T) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith K f) (hg : Continuous g)
    (hfs : ∀ p, (R : ℝ) < ‖p‖ → f p = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1) (v : I → ℝ) :
    LipschitzOnWith (pivotKernelLip J A R K * L * S)
      (fun x => pivotOutputDensity A (splitFreeColumns B (C x)) (splitFreeProfile f g) v) T := by
  have hρ := pivotOutputDensity_lipschitz A B R K hf hfs
  have he : (fun x => pivotOutputDensity A (splitFreeColumns B (C x)) (splitFreeProfile f g) v) =
      (fun x => ∫ n, g n * pivotOutputDensity A B f (v-C x n)) :=
    funext (fun x => splitPivotDensity_formula A B (C x) hf.continuous hg hfs hgs v)
  rw [he]
  apply fixedKernelMixture_lipschitzOn volume g _ T _ (compactBox_integrable g hg S hgs) hg0 hgmass
  · intro x _
    exact compactBox_integrable _ (hg.mul (hρ.continuous.comp (by fun_prop))) S
      (fun n hn => by rw [hgs n hn, zero_mul])
  · intro n hn
    have hnS : ‖n‖ ≤ S := le_of_not_gt (fun h => hn (hgs n h))
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hdiff : dist (C x n) (C y n) ≤ (L : ℝ)*dist x y*S := by
      rw [dist_eq_norm]
      have hop : ‖C x n-C y n‖ ≤ ‖C x-C y‖*‖n‖ := (C x-C y).le_opNorm n
      have hxy : ‖C x-C y‖ ≤ (L : ℝ)*dist x y := by
        simpa only [dist_eq_norm] using hC.dist_le_mul x hx y hy
      exact hop.trans (mul_le_mul hxy hnS (norm_nonneg _) (by positivity))
    apply (hρ.dist_le_mul (v-C x n) (v-C y n)).trans
    rw [dist_sub_left]
    apply (mul_le_mul_of_nonneg_left hdiff (pivotKernelLip J A R K).coe_nonneg).trans_eq
    simp only [NNReal.coe_mul]
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.NormalizedJetDensitySupport
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem normalizedJetDensity_bounds {Z P K α I J N : Type*}
    [Fintype P] [DecidableEq P] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ P) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (R H Kf S : ℝ≥0) {f : (J → ℝ) × (I → ℝ) → ℝ} {g : (N → ℝ) → ℝ}
    (hf : LipschitzWith Kf f) (hg : Continuous g)
    (hfs : ∀ u, (R : ℝ) < ‖u‖ → f u = 0) (hgs : ∀ n, (S : ℝ) < ‖n‖ → g n = 0)
    (hfb : ∀ u, ‖f u‖ ≤ H) (hg0 : ∀ n, 0 ≤ g n) (hgmass : (∫ n, g n) = 1) (v : I → ℝ) :
    (∀ x, ‖normalizedJetDensity A F e input z rows f g x v‖ ≤ pivotKernelCap J A R H) ∧
    LipschitzOnWith (pivotKernelLip J A R Kf *
      (Fintype.card N * polynomialBoxLip (Fintype.card P) degree (normalizedJetMass α degree)) * S)
      (fun x => normalizedJetDensity A F e input z rows f g x v) (Metric.closedBall 0 1) := by
  constructor
  · intro x
    exact splitPivotDensity_norm_le_cap A F _ R H S hf.continuous hg hfs hgs hfb hg0 hgmass v
  · exact splitPivotDensity_parameter_lipschitzOn A F _ (Metric.closedBall 0 1) _ R Kf S
      (normalizedJetColumns_lipschitzOn_box e input z hz rows hd) hf hg hfs hgs hg0 hgmass v

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

theorem affineProductProfile_integral {I : Type*} [Fintype I] (c w : I → ℝ)
    (hw : ∀ i, 0 < w i) : (∫ x, affineProductProfile c w x) = 1 := by
  change (∫ x, tensorCutoffWeight (fun i => affineProbabilityProfile (c i) (w i)) x) = 1
  rw [tensorCutoffWeight_integral]
  simp only [affineProbabilityProfile_integral _ (hw _), Finset.prod_const_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem affineSelectedJetDensity_bounds {Z X K α I J N : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1)
    (rows : I → Finset α) {degree : ℕ} (hd : ∀ n, (e n).sum (fun _ k => k) ≤ degree)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) {δ : ℝ≥0} (hδ : 0 < δ)
    (hwidth : ∀ j, (δ : ℝ) ≤ w (.inl j)) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R)
    (v : I → ℝ) :
    (∀ x, ‖affineSelectedJetDensity s A F e input z rows c w x v‖ ≤
      pivotKernelCap (UnselectedColumn s) A R (δ⁻¹^Fintype.card J)) ∧
    LipschitzOnWith (pivotKernelLip (UnselectedColumn s) A R (affineProductProfileLip J δ) *
      (Fintype.card N * polynomialBoxLip (Fintype.card X) degree (normalizedJetMass α degree)) * R)
      (fun x => affineSelectedJetDensity s A F e input z rows c w x v) (Metric.closedBall 0 1) := by
  have hcap := affineProductProfile_cap (fun j => c (.inl j)) (fun j => w (.inl j))
    (show (0 : ℝ) < δ from hδ) hwidth
  have hcap' : ∀ x, ‖affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j)) x‖ ≤
      ((δ⁻¹^Fintype.card J : ℝ≥0) : ℝ) := by
    simpa only [NNReal.coe_pow, NNReal.coe_inv] using hcap
  exact normalizedJetDensity_bounds A F e input z hz rows hd R (δ⁻¹^Fintype.card J)
    (affineProductProfileLip J δ) R
    (selectedCoefficientProfile_lipschitz s (affineProductProfile_lipschitz _ _ hδ hwidth))
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun j => hw (.inl j)) R.coe_nonneg (fun j => hsupport (.inl j))))
    (affineProductProfile_zero_outside _ _ (fun n => hw (.inr n)) R.coe_nonneg (fun n => hsupport (.inr n)))
    (selectedCoefficientProfile_norm_le s hcap')
    (affineProductProfile_nonneg _ _ (fun n => hw (.inr n)))
    (affineProductProfile_integral _ _ (fun n => hw (.inr n))) v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3

theorem principalTupleNormalized_norm_le {D α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (y : PrincipalIntegerTuples B h α L) : ‖principalTupleNormalized L y‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro a
  exact (norm_le_pi_norm (fun i => (y ⟨a.1, a.2.1, a.2.2.1⟩ i : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩) a.2.2.2).trans
    (integerScalarCubeBox_normalized_norm_le (hL _) (y _))

end Erdos3

end

section

namespace Erdos3

variable {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}

theorem partitionedPrincipalInput_frozen_bound [Fintype D] [∀ d, Fintype (B d)]
    [Fintype α] [DecidableEq α] (P : D → Prop) [DecidablePred P]
    (zr : Z → ℝ) (hz : ∀ j, |zr j| ≤ 1)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (u : PrincipalAxisTuples (α := α) P L)
    (j : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) :
    |Sum.elim zr (principalTupleNormalized (principalAxisLength P L) u) j| ≤ 1 := by
  cases j with
  | inl j => exact hz j
  | inr j =>
    have hb : ‖principalTupleNormalized (principalAxisLength P L) u‖ ≤ 1 :=
      principalTupleNormalized_norm_le
        (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (fun k => hL ⟨k.1.val, k.2⟩) u
    exact (norm_le_pi_norm (principalTupleNormalized (principalAxisLength P L) u) j).trans hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

omit [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)] in
theorem allocatedNonkernelExponent_degree (j : Fin m) (d : AllocatedNonkernelCoefficient (G := G) B j) :
    (allocatedNonkernelExponent B j d).sum (fun _ r => r) ≤ j.val+1 := d.val.property

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

include hR hσ in
theorem allocatedContinuousProfileWidths_pos (j : Fin m) (i : I j) (d) :
    0 < allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  coefficientProfileWidth_pos _ _ (div_pos (hR j) (by norm_num))
    (principalProfileSize_pos (hR j) _) (tailProfileSize_pos (hR j) (hσ j) _) d

include hR hσ in
theorem allocatedContinuousProfile_bound (j : Fin m) (i : I j) (hσ1 : σ j ≤ 1) (d) :
    |allocatedContinuousProfileCenters (G := G) B R j i d| +
      allocatedContinuousProfileWidths B R σ j i d ≤ R j :=
  (allocatedProfile_term_bound (layerContinuousPrincipalSlots B j i) (constantCoefficientSlot _ _)
    (layerContinuousPrincipalSlots_not_constant B j i) (hR j) (hσ j) hσ1 d).trans (by linarith [hR j])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators Matrix Classical

theorem allocatedUnitProfileWidth_le {J : Type*} [Fintype J] (P : Finset J) (j₀ : J)
    {R σ : ℝ} (hR : 0 < R) (j : J) :
    allocatedUnitProfileWidth R σ (Fintype.card J) ≤
      coefficientProfileWidth P j₀ (R/4) (principalProfileSize R P.card)
        (tailProfileSize R σ (Fintype.card J)) j := by
  have hp : principalProfileSize R (Fintype.card J) ≤ principalProfileSize R P.card := by
    unfold principalProfileSize
    apply div_le_div_of_nonneg_left hR.le (by positivity)
    gcongr
    exact_mod_cast P.card_le_univ
  simp only [allocatedUnitProfileWidth, allocatedWidthFloor, pow_zero, div_one]
  unfold coefficientProfileWidth
  split_ifs
  · exact min_le_left _ _
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (div_le_div_of_nonneg_right hp (by norm_num))
  · exact (min_le_right _ _).trans (min_le_right _ _)

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : I j)

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

include hR in
theorem allocatedContinuousProfileWidths_floor (d) :
    unitWidth ≤ allocatedContinuousProfileWidths (G := G) B R σ j i d :=
  allocatedUnitProfileWidth_le _ _ (hR j) d

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => 1)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) zero_lt_one (s o))
  (fun _ => zero_lt_one)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => 1))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" => NNReal.mk unitWidth (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

theorem allocatedPartitionedInput_frozen_bound (t) : |fixedReal t| ≤ 1 := by
  apply partitionedPrincipalInput_frozen_bound grid _ _ sides (allocatedPrincipalSides_pos B U basis S) u t
  intro ga
  have h := (norm_le_pi_norm (fun a => ((x ga.1 a : ℤ) : ℝ)/(S.value : ℝ)) ga.2).trans
    (integerScalarCubeBox_normalized_norm_le S.positive (x ga.1))
  simpa only [Real.norm_eq_abs] using h

include hR hσ in
theorem allocatedContinuousKernelDensity_bounds_s2_oai (hσ1 : σ j ≤ 1) (v : O → ℝ) :
    (∀ y, |allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v| ≤
      pivotKernelCap (UnselectedColumn s) pivot radius
        (delta⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1)))) ∧
      LipschitzOnWith
        (pivotKernelLip (UnselectedColumn s) pivot radius
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) delta) *
          (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
            polynomialBoxLip
              (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
                (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) * radius)
        (fun y => allocatedContinuousKernelDensity B U basis S j i x u rows s hA y v)
        (Metric.closedBall 0 1) := by
  have hδ : 0 < delta := allocatedUnitProfileWidth_pos (hR j) (hσ j) _
  have he := affineSelectedJetDensity_bounds s pivot free (allocatedNonkernelExponent B j)
    input fixedReal (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j) (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex d)) hδ
    (fun d => allocatedContinuousProfileWidths_floor B hR j i (reindex (.inl d))) radius
    (fun d => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex d)) v
  simpa only [allocatedContinuousKernelDensity, Real.norm_eq_abs] using he

end VectorPolynomial
end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_bounds_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
