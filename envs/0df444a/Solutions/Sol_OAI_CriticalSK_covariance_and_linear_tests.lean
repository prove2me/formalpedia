-- Prove2me | solution 1 for OAI.CriticalSK.covariance_and_linear_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:35:19.399371+00:00
-- url     : https://prove2.me/submissions/2d08d6d6-1394-4128-a805-6a21fa68a0e0

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_OAIQWCSK001
import Theorems.Thm_OAI_CriticalSK_natural_smallBall_tight
import Theorems.Thm_OAI_CriticalSK_cavity_overlap_tail_zero
import Theorems.Thm_OAI_CriticalSK_covariance_upper_tight

section
-- module Solutions.OAIQW_CriticalSK.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434


end OAI.CriticalSK
end

section
-- module Solutions.OAIQW_CriticalSK.Gibbs
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

section FiniteGibbs

variable {n : ℕ} (W : Disorder n)

lemma gibbs_sum : ∑ x : Spin n, gibbs W x = 1 := by
  unfold gibbs
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos W))

lemma mean_odd_eq_zero (f : Spin n → ℝ) (hf : ∀ x, f (spinFlip x) = -f x) :
    mean W f = 0 := by
  have h : mean W f = -mean W f := by
    calc
      mean W f = ∑ x, gibbs W (spinFlip x) * f (spinFlip x) :=
        (Equiv.sum_comp spinFlipEquiv (fun x => gibbs W x * f x)).symm
      _ = -mean W f := by simp [hf, mean, Finset.sum_neg_distrib]
  linarith

@[simp] lemma mean_spin (i : Fin n) : mean W (fun x => spinValue (x i)) = 0 := by
  apply mean_odd_eq_zero
  intro x
  simp [spinFlip]

@[simp] lemma mean_linearObservable (a : Fin n → ℝ) :
    mean W (linearObservable a) = 0 :=
  mean_odd_eq_zero W _ (linearObservable_spinFlip a)

lemma covariance_eq (i j : Fin n) :
    covariance W i j = mean W (fun x => spinValue (x i) * spinValue (x j)) := by
  simp [covariance]

@[simp] lemma covariance_diag (i : Fin n) : covariance W i i = 1 := by
  rw [covariance_eq]
  simpa [mean, ← sq] using gibbs_sum W

lemma sameExcept_refl (i : Fin n) (x : Spin n) : sameExcept i x x := by
  intro _ _
  rfl

lemma fiberMass_pos (i : Fin n) (x : Spin n) : 0 < fiberMass W i x := by
  have h : gibbs W x ≤ fiberMass W i x := by
    unfold fiberMass
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun z => if sameExcept i x z then gibbs W z else 0)
      (fun z _ => by split_ifs; exact gibbs_nonneg W z; exact le_rfl) (Finset.mem_univ x)
    simpa only [sameExcept_refl, ite_true] using hh
  exact lt_of_lt_of_le (gibbs_pos W x) h

lemma siteKernel_sum (i : Fin n) (x : Spin n) : ∑ y, siteKernel W i x y = 1 := by
  calc
    (∑ y, siteKernel W i x y) = fiberMass W i x / fiberMass W i x := by
      unfold siteKernel fiberMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> simp
    _ = 1 := div_self (ne_of_gt (fiberMass_pos W i x))

lemma siteKernel_same_row {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    siteKernel W i x = siteKernel W i y := by
  funext z
  change (if sameExcept i x z then gibbs W z / fiberMass W i x else 0) =
    (if sameExcept i y z then gibbs W z / fiberMass W i y else 0)
  simp only [sameExcept_classes h z, fiberMass_eq W h]

lemma siteKernel_projection (i : Fin n) : siteKernel W i * siteKernel W i = siteKernel W i := by
  ext x z
  change (∑ y, siteKernel W i x y * siteKernel W i y z) = siteKernel W i x z
  calc
    (∑ y, siteKernel W i x y * siteKernel W i y z) =
        ∑ y, siteKernel W i x y * siteKernel W i x z := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : sameExcept i x y
      · rw [siteKernel_same_row W h]
      · simp [siteKernel, h]
    _ = siteKernel W i x z := by rw [← Finset.sum_mul, siteKernel_sum, one_mul]

end FiniteGibbs

variable {n : ℕ} (W : Disorder n)

lemma mean_nonneg {f : Spin n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean W f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (gibbs_nonneg W x) (hf x))

lemma mean_mono {f g : Spin n → ℝ} (h : ∀ x, f x ≤ g x) : mean W f ≤ mean W g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (gibbs_nonneg W x))

@[simp] lemma mean_const (c : ℝ) : mean W (fun _ => c) = c := by
  simp only [mean, ← Finset.sum_mul, gibbs_sum, one_mul]

lemma mean_add (f g : Spin n → ℝ) :
    mean W (fun x => f x + g x) = mean W f + mean W g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (f g : Spin n → ℝ) :
    mean W (fun x => f x - g x) = mean W f - mean W g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul_const (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => f x * c) = mean W f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

lemma mean_const_mul (f : Spin n → ℝ) (c : ℝ) :
    mean W (fun x => c * f x) = c * mean W f := by
  simpa only [mul_comm c] using mean_mul_const W f c

lemma siteAverage_eq (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    siteAverage W i f x = ∑ y, siteKernel W i x y * f y := rfl

lemma siteAverage_add (i : Fin n) (f g : Spin n → ℝ) :
    siteAverage W i (fun x => f x + g x) =
      fun x => siteAverage W i f x + siteAverage W i g x :=
  Matrix.mulVec_add _ _ _

lemma siteAverage_sub (i : Fin n) (f g : Spin n → ℝ) :
    siteAverage W i (fun x => f x - g x) =
      fun x => siteAverage W i f x - siteAverage W i g x := by
  funext x
  simp only [siteAverage_eq, mul_sub, Finset.sum_sub_distrib]

lemma siteAverage_idempotent (i : Fin n) (f : Spin n → ℝ) :
    siteAverage W i (siteAverage W i f) = siteAverage W i f := by
  unfold siteAverage
  rw [Matrix.mulVec_mulVec, siteKernel_projection]

lemma siteAverage_of_fiber_constant (i : Fin n) (f : Spin n → ℝ)
    (hf : ∀ x y, sameExcept i x y → f y = f x) : siteAverage W i f = f := by
  funext x
  calc
    siteAverage W i f x = ∑ y, siteKernel W i x y * f x := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : sameExcept i x y
      · rw [hf x y h]
      · simp [siteKernel, h]
    _ = f x := by rw [← Finset.sum_mul, siteKernel_sum, one_mul]

lemma siteAverage_selfadjoint (i : Fin n) (f g : Spin n → ℝ) :
    mean W (fun x => f x * siteAverage W i g x) =
      mean W (fun x => siteAverage W i f x * g x) := by
  simp only [mean, siteAverage_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    gibbs W y * (f y * (siteKernel W i y x * g x)) =
      (gibbs W y * siteKernel W i y x) * (f y * g x) := by ring
    _ = (gibbs W x * siteKernel W i x y) * (f y * g x) := by
      rw [siteKernel_reversible]
    _ = gibbs W x * (siteKernel W i x y * f y * g x) := by ring

lemma siteAverage_orthogonal (i : Fin n) (f g : Spin n → ℝ)
    (hg : siteAverage W i g = g) :
    mean W (fun x => (f x - siteAverage W i f x) * g x) = 0 := by
  have h := siteAverage_selfadjoint W i f g
  rw [hg] at h
  simp only [sub_mul, mean_sub]
  exact sub_eq_zero.mpr h

theorem siteAverage_least_squares (i : Fin n) (f g : Spin n → ℝ)
    (hg : ∀ x y, sameExcept i x y → g y = g x) :
    mean W (fun x => (f x - siteAverage W i f x) ^ 2) ≤
      mean W (fun x => (f x - g x) ^ 2) := by
  have hfixed : siteAverage W i (fun x => siteAverage W i f x - g x) =
      (fun x => siteAverage W i f x - g x) := by
    rw [siteAverage_sub, siteAverage_idempotent, siteAverage_of_fiber_constant W i g hg]
  have horth := siteAverage_orthogonal W i f _ hfixed
  have hexpand : mean W (fun x => (f x - g x) ^ 2) =
      mean W (fun x => (f x - siteAverage W i f x) ^ 2) +
      mean W (fun x => (siteAverage W i f x - g x) ^ 2) +
      2 * mean W (fun x => (f x - siteAverage W i f x) * (siteAverage W i f x - g x)) := by
    rw [← mean_const_mul, ← mean_add, ← mean_add]
    congr 1
    funext x
    ring
  rw [horth, mul_zero, add_zero] at hexpand
  have hnonneg := mean_nonneg W (fun x => sq_nonneg (siteAverage W i f x - g x))
  linarith

lemma siteAverage_form_identity (i : Fin n) (f : Spin n → ℝ) :
    mean W (fun x => (f x - siteAverage W i f x) ^ 2) =
      mean W (fun x => f x * (f x - siteAverage W i f x)) := by
  have hfixed := siteAverage_idempotent W i f
  have horth := siteAverage_orthogonal W i f _ hfixed
  have hexpand : mean W (fun x => f x * (f x - siteAverage W i f x)) =
      mean W (fun x => (f x - siteAverage W i f x) ^ 2) +
      mean W (fun x => (f x - siteAverage W i f x) * siteAverage W i f x) := by
    rw [← mean_add]
    congr 1
    funext x
    ring
  linarith

lemma linearObservable_split (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    linearObservable a x = a i * spinValue (x i) + linearRest a i x := by
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

lemma linearRest_fiber_constant (a : Fin n → ℝ) (i : Fin n) (x y : Spin n)
    (h : sameExcept i x y) : linearRest a i y = linearRest a i x := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.ne_of_mem_erase hj)]

theorem dirichlet_linear_le (a : Fin n → ℝ) :
    dirichlet W (linearObservable a) ≤ ∑ i : Fin n, a i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  calc
    mean W (fun x => (linearObservable a x - ∑ y, siteKernel W i x y * linearObservable a y) ^ 2)
        ≤ mean W (fun x => (linearObservable a x - linearRest a i x) ^ 2) :=
      siteAverage_least_squares W i _ _ (linearRest_fiber_constant a i)
    _ = a i ^ 2 := by
      simp_rw [linearObservable_split a i, add_sub_cancel_right, mul_pow, spinValue_sq, mul_one]
      exact mean_const W _

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.HeatBath
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

open scoped InnerProductSpace

section GibbsEuclidean

variable {n : ℕ} (W : Disorder n)

lemma siteAverage_self_square (i : Fin n) (f : Spin n → ℝ) :
    mean W (fun x => f x * siteAverage W i f x) =
      mean W (fun x => (siteAverage W i f x) ^ 2) := by
  have h := siteAverage_selfadjoint W i f (siteAverage W i f)
  simpa only [siteAverage_idempotent, sq] using h

end GibbsEuclidean

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.SphereGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
namespace CriticalSK


section

lemma spinValue_beq (a b : Bool) : spinValue (a == b) = spinValue a * spinValue b := by
  cases a <;> cases b <;> norm_num [spinValue]

lemma cubeOverlap_signMean {n : ℕ} (x y : Spin n) :
    cubeOverlap x y = signMean (spinProduct x y) := by
  unfold cubeOverlap signMean cubeVector
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial, dotProduct, spinProduct, spinValue_beq, mul_comm]

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Cavity
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory

variable {n : ℕ}

lemma flipSite_ne (i : Fin n) (x : Spin n) : flipSite i x ≠ x := by
  intro hh
  have he := congrFun hh i
  simp only [flipSite_apply_self] at he
  cases h : x i <;> simp_all

lemma sameExcept_flipSite (i : Fin n) (x : Spin n) : sameExcept i x (flipSite i x) := by
  intro j hj
  exact flipSite_apply_ne i x hj

lemma sameExcept_two (i : Fin n) (x y : Spin n) :
    sameExcept i x y ↔ y=x ∨ y=flipSite i x := by
  constructor
  · intro h
    by_cases he : y i=x i
    · left
      funext j
      by_cases hj : j=i
      · simpa only [hj] using he
      · exact h j hj
    · right
      funext j
      by_cases hj : j=i
      · subst j
        simp only [flipSite_apply_self]
        cases hx : x i <;> cases hy : y i <;> simp_all
      · rw [flipSite_apply_ne i x hj]
        exact h j hj
  · rintro (h|h)
    · subst y; exact sameExcept_refl i x
    · subst y; exact sameExcept_flipSite i x

lemma sum_sameExcept (i : Fin n) (x : Spin n) (f : Spin n → ℝ) :
    (∑ y : Spin n, if sameExcept i x y then f y else 0) = f x+f (flipSite i x) := by
  classical
  have he (y : Spin n) : (if sameExcept i x y then f y else 0) =
      (if y=x then f x else 0)+(if y=flipSite i x then f (flipSite i x) else 0) := by
    simp only [sameExcept_two]
    have hne := flipSite_ne i x
    split_ifs <;> simp_all
  simp_rw [he]
  simp [Finset.sum_add_distrib]

lemma incidentCoeff_fiber {i : Fin n} {x y : Spin n} (h : sameExcept i x y) (e : Edge n) :
    incidentCoeff i y e = incidentCoeff i x e := by
  unfold incidentCoeff
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  split_ifs with h1 h2
  · rw [h e.val.2 (by grind)]
  · rw [h e.val.1 h1]
  · rfl

lemma localField_fiber (W : Disorder n) {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    localField W i y = localField W i x := by
  simp_rw [localField,incidentCoeff_fiber h]

lemma delete_hamiltonian_fiber (W : Disorder n) {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    hamiltonian (deleteDisorder W i) y = hamiltonian (deleteDisorder W i) x := by
  unfold hamiltonian deleteDisorder
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · simp
  · rw [h e.val.1 (fun hh => he (Or.inl hh)), h e.val.2 (fun hh => he (Or.inr hh))]

lemma hamiltonian_cavity (W : Disorder n) (i : Fin n) (x : Spin n) :
    hamiltonian W x = hamiltonian (deleteDisorder W i) x+spinValue (x i)*localField W i x := by
  simp only [hamiltonian,localField,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold deleteDisorder incidentCoeff
  by_cases h1 : e.val.1=i
  · simp [h1]; ring
  · by_cases h2 : e.val.2=i
    · simp [h1,h2]; ring
    · simp [h1,h2]

lemma gibbs_delete_fiber (W : Disorder n) {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    gibbs (deleteDisorder W i) y = gibbs (deleteDisorder W i) x := by
  simp only [gibbs,delete_hamiltonian_fiber W h]

lemma cavity_exp_pair (W : Disorder n) (i : Fin n) (x : Spin n) :
    (Real.exp (hamiltonian W x)+Real.exp (hamiltonian W (flipSite i x)))/2 =
      Real.exp (hamiltonian (deleteDisorder W i) x)*Real.cosh (localField W i x) := by
  rw [hamiltonian_cavity W i x,hamiltonian_cavity W i (flipSite i x),
    localField_fiber W (sameExcept_flipSite i x),delete_hamiltonian_fiber W (sameExcept_flipSite i x)]
  simp only [Real.exp_add,flipSite_apply_self,spinValue_not,Real.cosh_eq]
  cases x i <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,neg_neg] <;> ring

lemma cavityNormalization_ge_one (W : Disorder n) (i : Fin n) : 1 ≤ cavityNormalization W i := by
  rw [cavityNormalization,← mean_const (deleteDisorder W i) 1]
  exact mean_mono _ (fun _ => Real.one_le_cosh _)

lemma partition_cavity (W : Disorder n) (i : Fin n) :
    partition W = partition (deleteDisorder W i)*cavityNormalization W i := by
  have hh : ∑ x : Spin n, Real.exp (hamiltonian W (flipSite i x)) = partition W :=
    (flipSiteEquiv i).sum_comp (fun x => Real.exp (hamiltonian W x))
  have hs := congrArg (fun f : Spin n → ℝ => ∑ x, f x) (funext (cavity_exp_pair W i))
  rw [← Finset.sum_div,Finset.sum_add_distrib,hh] at hs
  change (partition W+partition W)/2 = _ at hs
  unfold cavityNormalization mean gibbs
  simp only [Finset.mul_sum]
  rw [show (fun x : Spin n => partition (deleteDisorder W i)*(Real.exp (hamiltonian (deleteDisorder W i) x)/partition (deleteDisorder W i)*Real.cosh (localField W i x))) =
    (fun x => Real.exp (hamiltonian (deleteDisorder W i) x)*Real.cosh (localField W i x)) by
      funext x
      field_simp [ne_of_gt (partition_pos (deleteDisorder W i))]]
  linarith

lemma gibbs_cavity (W : Disorder n) (i : Fin n) (x : Spin n) :
    gibbs W x = gibbs (deleteDisorder W i) x*Real.exp (spinValue (x i)*localField W i x)/cavityNormalization W i := by
  simp only [gibbs,partition_cavity W i,hamiltonian_cavity W i x,Real.exp_add]
  ring

lemma gibbs_cavity_pair (W : Disorder n) (i : Fin n) (x : Spin n) :
    (gibbs W x+gibbs W (flipSite i x))/2 =
      gibbs (deleteDisorder W i) x*Real.cosh (localField W i x)/cavityNormalization W i := by
  unfold gibbs
  rw [← add_div]
  rw [show (Real.exp (hamiltonian W x)+Real.exp (hamiltonian W (flipSite i x)))/partition W/2 =
    ((Real.exp (hamiltonian W x)+Real.exp (hamiltonian W (flipSite i x)))/2)/partition W by ring]
  rw [cavity_exp_pair,partition_cavity W i]
  ring

lemma mean_cavity_even (W : Disorder n) (i : Fin n) (f : Spin n → ℝ)
    (hf : ∀ x, f (flipSite i x)=f x) :
    mean W f = mean (deleteDisorder W i) (fun x => Real.cosh (localField W i x)*f x)/cavityNormalization W i := by
  have hh : ∑ x : Spin n, gibbs W (flipSite i x)*f (flipSite i x) = mean W f :=
    (flipSiteEquiv i).sum_comp (fun x => gibbs W x*f x)
  simp_rw [hf] at hh
  have hs := congrArg (fun g : Spin n → ℝ => ∑ x, g x) (funext (fun x => congrArg (fun a : ℝ => a*f x) (gibbs_cavity_pair W i x)))
  simp only [add_div,add_mul,div_mul_eq_mul_div,Finset.sum_add_distrib,← Finset.sum_div,hh] at hs
  unfold mean at *
  simp only [mul_assoc] at hs
  linarith

lemma siteAverage_two (W : Disorder n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    siteAverage W i f x = (gibbs W x*f x+gibbs W (flipSite i x)*f (flipSite i x))/(gibbs W x+gibbs W (flipSite i x)) := by
  rw [siteAverage_eq]
  simp only [siteKernel]
  have he (y : Spin n) : (if sameExcept i x y then gibbs W y/(∑ z, if sameExcept i x z then gibbs W z else 0) else 0)*f y =
      (if sameExcept i x y then gibbs W y*f y else 0)/(∑ z, if sameExcept i x z then gibbs W z else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [← Finset.sum_div,sum_sameExcept,sum_sameExcept]

lemma siteAverage_spin (W : Disorder n) (i : Fin n) (x : Spin n) :
    siteAverage W i (fun y => spinValue (y i)) x = Real.sinh (localField W i x)/Real.cosh (localField W i x) := by
  rw [siteAverage_two,gibbs_cavity W i x,gibbs_cavity W i (flipSite i x),
    gibbs_delete_fiber W (sameExcept_flipSite i x),localField_fiber W (sameExcept_flipSite i x)]
  have hg := ne_of_gt (gibbs_pos (deleteDisorder W i) x)
  have hZ : cavityNormalization W i ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (cavityNormalization_ge_one W i))
  rw [Real.sinh_eq,Real.cosh_eq]
  simp only [flipSite_apply_self,spinValue_not]
  cases x i <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,neg_neg] <;>
    field_simp [hg,hZ] <;> ring

lemma alphaSite_pos (W : Disorder n) (i : Fin n) : 0 < alphaSite W i := by
  unfold alphaSite mean
  exact Finset.sum_pos (fun _ _ => mul_pos (gibbs_pos W _) (sq_pos_of_pos (inv_pos.mpr (Real.cosh_pos _)))) Finset.univ_nonempty

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma mean_mul_mean_inv {f : Spin n → ℝ} (hf : ∀ x, 0 < f x) :
    1 ≤ mean W f*mean W (fun x => (f x)⁻¹) := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := gibbs W) (f := fun x => gibbs W x*f x) (g := fun x => gibbs W x*(f x)⁻¹)
    (fun x _ => mul_nonneg (gibbs_nonneg W x) (hf x).le)
    (fun x _ => mul_nonneg (gibbs_nonneg W x) (inv_nonneg.mpr (hf x).le))
    (fun x _ => by apply le_of_eq; field_simp [ne_of_gt (hf x)])
  simpa only [gibbs_sum,one_pow,mean] using hh

lemma alphaSite_cavity (i : Fin n) :
    alphaSite W i = mean (deleteDisorder W i) (fun x => (Real.cosh (localField W i x))⁻¹)/cavityNormalization W i := by
  rw [alphaSite,mean_cavity_even W i _ (fun x => by rw [localField_fiber W (sameExcept_flipSite i x)])]
  congr 1
  congr 1
  funext x
  field_simp

lemma alphaSite_normalization (i : Fin n) : 1 ≤ alphaSite W i*cavityNormalization W i^2 := by
  have hh := mean_mul_mean_inv (deleteDisorder W i) (fun x => Real.cosh_pos (localField W i x))
  rw [alphaSite_cavity]
  have hZ : cavityNormalization W i ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (cavityNormalization_ge_one W i))
  convert hh using 1
  dsimp only [cavityNormalization] at *
  field_simp

lemma one_sub_tanh_sq (z : ℝ) : 1-(Real.sinh z/Real.cosh z)^2 = (Real.cosh z)⁻¹^2 := by
  have hh := Real.cosh_sq_sub_sinh_sq z
  have hc := ne_of_gt (Real.cosh_pos z)
  field_simp
  nlinarith

lemma site_spin_variance (i : Fin n) :
    mean W (fun x => (spinValue (x i)-siteAverage W i (fun y => spinValue (y i)) x)^2) = alphaSite W i := by
  rw [siteAverage_form_identity]
  have he : (fun x : Spin n => spinValue (x i)*(spinValue (x i)-siteAverage W i (fun y => spinValue (y i)) x)) =
      (fun x => 1-spinValue (x i)*siteAverage W i (fun y => spinValue (y i)) x) := by
    funext x
    have hh := spinValue_sq (x i)
    nlinarith
  rw [he,mean_sub,siteAverage_self_square,← mean_sub]
  simp_rw [siteAverage_spin,one_sub_tanh_sq]
  rfl

lemma siteAverage_const_mul (i : Fin n) (c : ℝ) (f : Spin n → ℝ) :
    siteAverage W i (fun x => c*f x) = fun x => c*siteAverage W i f x := by
  funext x
  simp only [siteAverage_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma siteAverage_linear_residual (i : Fin n) (a : Fin n → ℝ) (x : Spin n) :
    linearObservable a x-siteAverage W i (linearObservable a) x =
      a i*(spinValue (x i)-siteAverage W i (fun y => spinValue (y i)) x) := by
  have he : linearObservable a = fun y => a i*spinValue (y i)+linearRest a i y :=
    funext (linearObservable_split a i)
  rw [he,siteAverage_add,siteAverage_const_mul,
    siteAverage_of_fiber_constant W i _ (linearRest_fiber_constant a i)]
  ring

lemma dirichlet_linear_eq (a : Fin n → ℝ) :
    dirichlet W (linearObservable a) = ∑ i, alphaSite W i*a i^2 := by
  unfold dirichlet
  simp_rw [← siteAverage_eq,siteAverage_linear_residual,mul_pow,mean_const_mul,site_spin_variance]
  congr 1
  funext i
  ring

lemma dirichlet_linear_pos {a : Fin n → ℝ} (ha : a ≠ 0) :
    0 < dirichlet W (linearObservable a) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp ha
  rw [dirichlet_linear_eq]
  apply Finset.sum_pos' (fun j _ => mul_nonneg (alphaSite_pos W j).le (sq_nonneg _))
  exact ⟨i,Finset.mem_univ i,mul_pos (alphaSite_pos W i) (sq_pos_of_ne_zero hi)⟩

lemma mean_delete_le (i : Fin n) (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hflip : ∀ x, f (flipSite i x)=f x) :
    mean (deleteDisorder W i) f ≤ cavityNormalization W i*mean W f := by
  rw [mean_cavity_even W i f hflip]
  have hZ : cavityNormalization W i ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (cavityNormalization_ge_one W i))
  rw [mul_div_cancel₀ _ hZ]
  exact mean_mono _ (fun x => le_mul_of_one_le_left (hf x) (Real.one_le_cosh _))

lemma cavityOverlapCoord_eq (i : Fin n) (x y : Spin n) :
    cavityOverlapCoord i x y = cubeOverlap x y-spinValue (x i)*spinValue (y i)/(n:ℝ) := by
  rw [cubeOverlap_signMean]
  unfold signMean cavityOverlapCoord
  simp only [spinProduct,spinValue_beq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

lemma cavityOverlapCoord_fiber_left {i : Fin n} {x x' : Spin n} (h : sameExcept i x x') (y : Spin n) :
    cavityOverlapCoord i x' y = cavityOverlapCoord i x y := by
  unfold cavityOverlapCoord
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.ne_of_mem_erase hj)]

lemma cavityOverlapCoord_comm (i : Fin n) (x y : Spin n) : cavityOverlapCoord i x y = cavityOverlapCoord i y x := by
  unfold cavityOverlapCoord
  simp only [mul_comm]

lemma cavityOverlap_nonneg (i : Fin n) : 0 ≤ cavityOverlap W i :=
  mean_nonneg _ (fun _ => mean_nonneg _ (fun _ => sq_nonneg _))

lemma cavityOverlap_compare (i : Fin n) :
    cavityOverlap W i ≤ 2*cavityNormalization W i^2*(gibbsOverlap W+(n:ℝ)⁻¹^2) := by
  have hZ := (cavityNormalization_ge_one W i).trans' zero_le_one
  have hfirst := mean_delete_le W i (fun x => mean (deleteDisorder W i) (fun y => cavityOverlapCoord i x y^2))
    (fun _ => mean_nonneg _ (fun _ => sq_nonneg _))
    (fun x => by simp_rw [cavityOverlapCoord_fiber_left (sameExcept_flipSite i x)])
  have hsecond (x : Spin n) := mean_delete_le W i (fun y => cavityOverlapCoord i x y^2)
    (fun _ => sq_nonneg _) (fun y => by rw [cavityOverlapCoord_comm i x (flipSite i y),
      cavityOverlapCoord_fiber_left (sameExcept_flipSite i y),cavityOverlapCoord_comm])
  have hpoint (x y : Spin n) : cavityOverlapCoord i x y^2 ≤ 2*(cubeOverlap x y)^2+2*(n:ℝ)⁻¹^2 := by
    rw [cavityOverlapCoord_eq]
    have hh : (spinValue (x i)*spinValue (y i)/(n:ℝ))^2 = (n:ℝ)⁻¹^2 := by
      rw [div_pow,mul_pow,spinValue_sq,spinValue_sq,one_mul,one_div,inv_pow]
    nlinarith [sq_nonneg (cubeOverlap x y+spinValue (x i)*spinValue (y i)/(n:ℝ))]
  have hQ : mean W (fun x => mean W (fun y => 2*(cubeOverlap x y)^2+2*(n:ℝ)⁻¹^2)) =
      2*gibbsOverlap W+2*(n:ℝ)⁻¹^2 := by
    simp_rw [mean_add,mean_const_mul,mean_const]
    unfold mean gibbsOverlap
    simp only [Finset.mul_sum,mul_assoc]
  calc
    cavityOverlap W i ≤ cavityNormalization W i*mean W (fun x => mean (deleteDisorder W i) (fun y => cavityOverlapCoord i x y^2)) := hfirst
    _ ≤ cavityNormalization W i*mean W (fun x => cavityNormalization W i*mean W (fun y => cavityOverlapCoord i x y^2)) :=
      mul_le_mul_of_nonneg_left (mean_mono W hsecond) hZ
    _ = cavityNormalization W i^2*mean W (fun x => mean W (fun y => cavityOverlapCoord i x y^2)) := by rw [mean_const_mul]; ring
    _ ≤ cavityNormalization W i^2*mean W (fun x => mean W (fun y => 2*(cubeOverlap x y)^2+2*(n:ℝ)⁻¹^2)) :=
      mul_le_mul_of_nonneg_left (mean_mono W (fun x => mean_mono W (hpoint x))) (sq_nonneg _)
    _ = _ := by rw [hQ]; ring

end

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

lemma incidentCoeff_other (i : Fin n) (x : Spin n) (e : Incident i) :
    incidentCoeff i x e.val = spinValue (x ((incidentOtherEquiv i) e).val) := by
  change incidentCoeff i x e.val = spinValue (x (otherEnd i e))
  unfold incidentCoeff otherEnd
  have he := e.property
  dsimp only [touches] at he
  split_ifs <;> grind

lemma sum_incident_other (i : Fin n) (f : Fin n → ℝ) :
    (∑ e : Incident i, f (otherEnd i e)) = ∑ j ∈ Finset.univ.erase i, f j := by
  calc
    _ = ∑ j : {j : Fin n // j ≠ i}, f j := (incidentOtherEquiv i).sum_comp _
    _ = _ := (Finset.sum_subtype (Finset.univ.erase i) (by intro j; simp [ne_comm]) f).symm

lemma incident_coeff_square (i : Fin n) (x : Spin n) :
    (∑ e : Incident i, incidentCoeff i x e.val^2) = (n:ℝ)-1 := by
  simp_rw [incidentCoeff_other]
  change (∑ e : Incident i, (spinValue (x (otherEnd i e)))^2) = _
  rw [sum_incident_other i (fun j => spinValue (x j)^2)]
  simp only [spinValue_sq,Finset.sum_const, nsmul_eq_mul,mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]

lemma incident_coeff_product (i : Fin n) (x y : Spin n) :
    (∑ e : Incident i, incidentCoeff i x e.val*incidentCoeff i y e.val) =
      (n:ℝ)*cavityOverlapCoord i x y := by
  simp_rw [incidentCoeff_other]
  change (∑ e : Incident i, spinValue (x (otherEnd i e))*spinValue (y (otherEnd i e))) = _
  rw [sum_incident_other i (fun j => spinValue (x j)*spinValue (y j)),cavityOverlapCoord,mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt i.isLt)))]

lemma cavitySplit_preserving (i : Fin n) :
    MeasurePreserving (cavitySplit i) (disorderLaw n) ((incidentLaw i).prod (nonincidentLaw i)) :=
  measurePreserving_piEquivPiSubtypeProd _ _

lemma cavityJoin_apply_incident (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) (e : Incident i) :
    (cavitySplit i).symm (u,v) e.val = u e := by
  simp [cavitySplit,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,e.property]

lemma cavityJoin_apply_nonincident (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) (e : Nonincident i) :
    (cavitySplit i).symm (u,v) e.val = v e := by
  simp [cavitySplit,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,e.property]

lemma delete_cavityJoin (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) :
    deleteDisorder ((cavitySplit i).symm (u,v)) i = (cavitySplit i).symm (0,v) := by
  funext e
  by_cases he : touches i e
  · rw [show e = (⟨e,he⟩ : Incident i).val from rfl,cavityJoin_apply_incident]
    simp only [deleteDisorder,ite_eq_left (show e.val.1=i ∨ e.val.2=i from he)]
    rfl
  · rw [show e = (⟨e,he⟩ : Nonincident i).val from rfl,cavityJoin_apply_nonincident]
    simp only [deleteDisorder,ite_eq_right (show ¬(e.val.1=i ∨ e.val.2=i) from he)]
    exact cavityJoin_apply_nonincident i u v ⟨e,he⟩

lemma localField_cavityJoin (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) (x : Spin n) :
    localField ((cavitySplit i).symm (u,v)) i x = ∑ e : Incident i, incidentCoeff i x e.val*u e := by
  unfold localField
  rw [← Fintype.sum_subtype_add_sum_subtype (touches i)]
  have hz : (∑ e : Nonincident i, (cavitySplit i).symm (u,v) e.val*incidentCoeff i x e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have he := e.property
    simp only [touches,not_or] at he
    simp [incidentCoeff,he.1,he.2]
  rw [hz,add_zero]
  simp_rw [cavityJoin_apply_incident,mul_comm]

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

lemma gaussianLinear_continuous (a : ι → ℝ) : Continuous (gaussianLinear a) := by
  unfold gaussianLinear
  fun_prop

lemma gaussian_exp_integrable (v : ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z => Real.exp (gaussianLinear a z)) (gaussianScalarPi v) := by
  simp only [gaussianLinear,Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

lemma gaussian_exp_integral (v : ℝ≥0) (a : ι → ℝ) :
    (∫ z, Real.exp (gaussianLinear a z) ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*(∑ i, a i^2)/2) := by
  simp only [gaussianLinear,Real.exp_sum,gaussianScalarPi]
  rw [integral_fintype_prod_eq_prod (μ := fun _ => gaussianReal 0 v) (fun i (z : ℝ) => Real.exp (a i*z))]
  have he (i : ι) : (∫ z : ℝ, Real.exp (a i*z) ∂gaussianReal 0 v) = Real.exp ((v:ℝ)*(a i)^2/2) := by
    have hh := mgf_gaussianReal (p := gaussianReal 0 v) (X := id) (μ := 0) (v := v) (by simp) (a i)
    simpa only [mgf,zero_mul,zero_add,id_eq] using hh
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_div]

lemma gaussianLinear_neg (a z : ι → ℝ) : gaussianLinear (-a) z = -gaussianLinear a z := by
  simp [gaussianLinear]

lemma gaussianLinear_add (a b z : ι → ℝ) : gaussianLinear (a+b) z = gaussianLinear a z+gaussianLinear b z := by
  simp [gaussianLinear,add_mul,Finset.sum_add_distrib]

lemma gaussianLinear_sub (a b z : ι → ℝ) : gaussianLinear (a-b) z = gaussianLinear a z-gaussianLinear b z := by
  simp [gaussianLinear,sub_mul,Finset.sum_sub_distrib]

lemma gaussian_cosh_integrable (v : ℝ≥0) (a : ι → ℝ) :
    Integrable (fun z => Real.cosh (gaussianLinear a z)) (gaussianScalarPi v) := by
  simp_rw [Real.cosh_eq,← gaussianLinear_neg]
  exact ((gaussian_exp_integrable v a).add (gaussian_exp_integrable v (-a))).div_const 2

lemma gaussian_cosh_integral (v : ℝ≥0) (a : ι → ℝ) :
    (∫ z, Real.cosh (gaussianLinear a z) ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*(∑ i, a i^2)/2) := by
  simp_rw [Real.cosh_eq,← gaussianLinear_neg]
  rw [integral_div,integral_add (gaussian_exp_integrable v a) (gaussian_exp_integrable v (-a)),gaussian_exp_integral,gaussian_exp_integral]
  simp only [Pi.neg_apply,neg_sq]
  ring

lemma cosh_mul_cosh_identity (a b : ℝ) : Real.cosh a*Real.cosh b = (Real.cosh (a+b)+Real.cosh (a-b))/2 := by
  rw [Real.cosh_add,Real.cosh_sub]
  ring

lemma gaussian_cosh_product_integrable (v : ℝ≥0) (a b : ι → ℝ) :
    Integrable (fun z => Real.cosh (gaussianLinear a z)*Real.cosh (gaussianLinear b z)) (gaussianScalarPi v) := by
  simp_rw [cosh_mul_cosh_identity,← gaussianLinear_add,← gaussianLinear_sub]
  exact ((gaussian_cosh_integrable v (a+b)).add (gaussian_cosh_integrable v (a-b))).div_const 2

lemma gaussian_cosh_product_integral (v : ℝ≥0) (a b : ι → ℝ) :
    (∫ z, Real.cosh (gaussianLinear a z)*Real.cosh (gaussianLinear b z) ∂gaussianScalarPi v) =
      Real.exp ((v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2))/2)*Real.cosh ((v:ℝ)*∑ i, a i*b i) := by
  simp_rw [cosh_mul_cosh_identity,← gaussianLinear_add,← gaussianLinear_sub]
  rw [integral_div,integral_add (gaussian_cosh_integrable v (a+b)) (gaussian_cosh_integrable v (a-b)),gaussian_cosh_integral,gaussian_cosh_integral]
  have hp : (∑ i, (a+b) i^2) = (∑ i, a i^2)+(∑ i, b i^2)+2*∑ i, a i*b i := by
    simp only [Pi.add_apply,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hm : (∑ i, (a-b) i^2) = (∑ i, a i^2)+(∑ i, b i^2)-2*∑ i, a i*b i := by
    simp only [Pi.sub_apply,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hp,hm,Real.cosh_eq]
  rw [show (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2)+2*∑ i, a i*b i)/2 =
    (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2))/2+(v:ℝ)*∑ i, a i*b i by ring,
    show (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2)-2*∑ i, a i*b i)/2 =
    (v:ℝ)*((∑ i, a i^2)+(∑ i, b i^2))/2+(-((v:ℝ)*∑ i, a i*b i)) by ring,
    Real.exp_add,Real.exp_add]
  ring

lemma cosh_pow_exp_bound (z : ℝ) (m : ℕ) :
    Real.cosh z^m ≤ Real.exp ((m:ℝ)*z)+Real.exp (-((m:ℝ)*z)) := by
  have hc : Real.cosh z ≤ Real.exp |z| := by
    rw [Real.cosh_eq]
    have hp := Real.exp_le_exp.mpr (le_abs_self z)
    have hm := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  have hh := pow_le_pow_left₀ (Real.cosh_pos z).le hc m
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans (by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz]
      linarith [Real.exp_pos (-((m:ℝ)*z))]
    · rw [abs_of_neg (lt_of_not_ge hz),mul_neg]
      linarith [Real.exp_pos ((m:ℝ)*z)])

lemma gaussian_cosh_pow_bound (v : ℝ≥0) (a : ι → ℝ) (m : ℕ) :
    Integrable (fun z => Real.cosh (gaussianLinear a z)^m) (gaussianScalarPi v) ∧
    (∫ z, Real.cosh (gaussianLinear a z)^m ∂gaussianScalarPi v) ≤
      2*Real.exp ((m:ℝ)^2*(v:ℝ)*(∑ i, a i^2)/2) := by
  let b : ι → ℝ := fun i => (m:ℝ)*a i
  have he (z : ι → ℝ) : gaussianLinear b z = (m:ℝ)*gaussianLinear a z := by
    simp only [gaussianLinear,b,Finset.mul_sum,mul_assoc]
  have hib := (gaussian_exp_integrable v b).add (gaussian_exp_integrable v (-b))
  have hi : Integrable (fun z => Real.cosh (gaussianLinear a z)^m) (gaussianScalarPi v) := by
    apply hib.mono' (((Real.continuous_cosh.comp (gaussianLinear_continuous a)).pow m).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Pi.add_apply, Pi.pow_apply, Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _),gaussianLinear_neg,he]
      exact cosh_pow_exp_bound _ _)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z, Real.exp (gaussianLinear b z)+Real.exp (gaussianLinear (-b) z) ∂gaussianScalarPi v :=
      integral_mono hi hib (fun z => by rw [gaussianLinear_neg,he]; exact cosh_pow_exp_bound _ _)
    _ = _ := by
      rw [integral_add (gaussian_exp_integrable v b) (gaussian_exp_integrable v (-b)),gaussian_exp_integral,gaussian_exp_integral]
      simp only [Pi.neg_apply,neg_sq,b,mul_pow,← Finset.mul_sum]
      ring_nf

lemma cosh_sub_one_quadratic {z : ℝ} (hz : |z| ≤ 1) : Real.cosh z-1 ≤ (Real.exp 1-1)*z^2 := by
  have hz2 : z^2 ≤ 1 := by nlinarith [sq_abs z,abs_nonneg z]
  have hc := (convexOn_exp.2 (show (0:ℝ) ∈ univ from trivial) (show (1:ℝ) ∈ univ from trivial)
    (show 0 ≤ 1-z^2 by nlinarith) (sq_nonneg z) (by ring))
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,Real.exp_zero] at hc
  have he := (Real.cosh_le_exp_half_sq z).trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg z] : z^2/2 ≤ z^2))
  nlinarith

end

open Set Filter MeasureTheory ProbabilityTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma coshMixture_continuous (p : κ → ℝ) (a : κ → ι → ℝ) : Continuous (coshMixture p a) := by
  unfold coshMixture
  apply continuous_finsetSum
  intro x _
  exact continuous_const.mul (Real.continuous_cosh.comp (gaussianLinear_continuous _))

lemma coshMixture_nonneg {p : κ → ℝ} (hp : ∀ x, 0 ≤ p x) (a : κ → ι → ℝ) (z : ι → ℝ) : 0 ≤ coshMixture p a z := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (Real.cosh_pos _).le)

lemma coshMixture_integrable (v : ℝ≥0) (p : κ → ℝ) (a : κ → ι → ℝ) :
    Integrable (coshMixture p a) (gaussianScalarPi v) :=
  integrable_finsetSum _ (fun x _ => (gaussian_cosh_integrable v (a x)).const_mul (p x))

lemma coshMixture_integral (v : ℝ≥0) {p : κ → ℝ} (hpsum : ∑ x, p x = 1)
    (a : κ → ι → ℝ) {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s) :
    (∫ z, coshMixture p a z ∂gaussianScalarPi v) = Real.exp ((v:ℝ)*s/2) := by
  unfold coshMixture
  rw [integral_finsetSum _ (fun x _ => (gaussian_cosh_integrable v (a x)).const_mul (p x))]
  simp_rw [integral_const_mul,gaussian_cosh_integral,hs]
  rw [← Finset.sum_mul,hpsum,one_mul]

lemma coshMixture_pow_integrable_bound (v : ℝ≥0) {p : κ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hpsum : ∑ x, p x = 1) (a : κ → ι → ℝ) {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s) (m : ℕ) :
    Integrable (fun z => coshMixture p a z^m) (gaussianScalarPi v) ∧
    (∫ z, coshMixture p a z^m ∂gaussianScalarPi v) ≤ 2*Real.exp ((m:ℝ)^2*(v:ℝ)*s/2) := by
  have hib : Integrable (fun z => ∑ x, p x*Real.cosh (gaussianLinear (a x) z)^m) (gaussianScalarPi v) :=
    integrable_finsetSum _ (fun x _ => ((gaussian_cosh_pow_bound v (a x) m).1.const_mul _))
  have hbound (z : ι → ℝ) : coshMixture p a z^m ≤ ∑ x, p x*Real.cosh (gaussianLinear (a x) z)^m :=
    Real.pow_arith_mean_le_arith_mean_pow _ _ _ (fun x _ => hp x) hpsum (fun _ _ => (Real.cosh_pos _).le) m
  have hi : Integrable (fun z => coshMixture p a z^m) (gaussianScalarPi v) := by
    apply hib.mono' ((coshMixture_continuous p a).pow m).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun z => by simp only [Pi.pow_apply]; rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (coshMixture_nonneg hp a z) _)]; exact hbound z)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z, ∑ x, p x*Real.cosh (gaussianLinear (a x) z)^m ∂gaussianScalarPi v := integral_mono hi hib hbound
    _ = ∑ x, p x*(∫ z, Real.cosh (gaussianLinear (a x) z)^m ∂gaussianScalarPi v) := by
      rw [integral_finsetSum _ (fun x _ => ((gaussian_cosh_pow_bound v (a x) m).1.const_mul _))]
      simp only [integral_const_mul]
    _ ≤ ∑ x, p x*(2*Real.exp ((m:ℝ)^2*(v:ℝ)*s/2)) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hp x)
      simpa only [hs] using (gaussian_cosh_pow_bound v (a x) m).2
    _ = _ := by rw [← Finset.sum_mul,hpsum,one_mul]

lemma coshMixture_square (p : κ → ℝ) (a : κ → ι → ℝ) (z : ι → ℝ) :
    coshMixture p a z^2 = ∑ x, ∑ y, p x*p y*(Real.cosh (gaussianLinear (a x) z)*Real.cosh (gaussianLinear (a y) z)) := by
  simp only [coshMixture,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma coshMixture_square_integral (v : ℝ≥0) (p : κ → ℝ) (a : κ → ι → ℝ)
    {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s) :
    (∫ z, coshMixture p a z^2 ∂gaussianScalarPi v) =
      Real.exp ((v:ℝ)*s)*(∑ x, ∑ y, p x*p y*Real.cosh ((v:ℝ)*∑ i, a x i*a y i)) := by
  simp_rw [coshMixture_square]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (gaussian_cosh_product_integrable v (a x) (a y)).const_mul (p x*p y)))]
  simp_rw [integral_finsetSum _ (fun y _ => (gaussian_cosh_product_integrable v _ (a y)).const_mul _),integral_const_mul,gaussian_cosh_product_integral,hs]
  rw [show (v:ℝ)*(s+s)/2 = (v:ℝ)*s by ring]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma coshMixture_centered_integrable_bound (v : ℝ≥0) {p : κ → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hpsum : ∑ x, p x = 1) (a : κ → ι → ℝ) {s : ℝ} (hs : ∀ x, ∑ i, a x i^2 = s)
    (hc : ∀ x y, |(v:ℝ)*∑ i, a x i*a y i| ≤ 1) :
    Integrable (fun z => (coshMixture p a z-Real.exp ((v:ℝ)*s/2))^2) (gaussianScalarPi v) ∧
    (∫ z, (coshMixture p a z-Real.exp ((v:ℝ)*s/2))^2 ∂gaussianScalarPi v) ≤
      Real.exp ((v:ℝ)*s)*(Real.exp 1-1)*(∑ x, ∑ y, p x*p y*((v:ℝ)*∑ i, a x i*a y i)^2) := by
  let m := Real.exp ((v:ℝ)*s/2)
  have hi := (coshMixture_pow_integrable_bound v hp hpsum a hs 2).1
  have hmi := coshMixture_integrable v p a
  have he (z : ι → ℝ) : (coshMixture p a z-m)^2 = coshMixture p a z^2-2*m*coshMixture p a z+m^2 := by ring
  have hiz : Integrable (fun z => (coshMixture p a z-m)^2) (gaussianScalarPi v) := by
    simp_rw [he]
    exact (hi.sub (hmi.const_mul _)).add (integrable_const _)
  refine ⟨hiz,?_⟩
  have hm2 : m^2 = Real.exp ((v:ℝ)*s) := by dsimp only [m]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsum : (∑ x, ∑ y, p x*p y) = 1 := by simp only [← Finset.mul_sum,hpsum,mul_one]
  have hid : (∫ z, (coshMixture p a z-m)^2 ∂gaussianScalarPi v) =
      Real.exp ((v:ℝ)*s)*(∑ x, ∑ y, p x*p y*(Real.cosh ((v:ℝ)*∑ i, a x i*a y i)-1)) := by
    simp_rw [he]
    rw [integral_add (f := fun z => coshMixture p a z^2-2*m*coshMixture p a z) (g := fun _ => m^2) (hi.sub (hmi.const_mul _)) (integrable_const _),integral_sub (f := fun z => coshMixture p a z^2) (g := fun z => 2*m*coshMixture p a z) hi (hmi.const_mul _),integral_const_mul,
      coshMixture_integral v hpsum a hs,coshMixture_square_integral v p a hs,integral_const,probReal_univ,one_smul]
    change Real.exp ((v:ℝ)*s)*_-2*m*m+m^2 = _
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hsum]
    nlinarith
  rw [hid]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  nlinarith [mul_le_mul_of_nonneg_left (cosh_sub_one_quadratic (hc x y)) (mul_nonneg (hp x) (hp y))]

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.CubeRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set
namespace CriticalSK

lemma integral_dominates_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {E : Set Ω} {f : Ω → ℝ}
    (hi : Integrable f μ) (hf : ∀ x, 0 ≤ f x) (he : ∀ x ∈ E, 1 ≤ f x) :
    μ.real E ≤ ∫ x, f x ∂μ := by
  apply (measureReal_mono (show E ⊆ {x | 1 ≤ f x} from he)).trans
  simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hf) hi 1

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

open Set MeasureTheory Filter

lemma third_power_square {x : ℝ} (hx : 0 ≤ x) : (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.DisorderTransfer
attribute [-instance] _root_.OAI.CriticalSK.disorderLaw_probability _root_.OAI.CriticalSK.instDecidablePredEdgeTouches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set

namespace CriticalSK

section

lemma gibbs_continuous {n : ℕ} (x : Spin n) : Continuous (fun W : Disorder n => gibbs W x) := by
  apply Continuous.div
  · unfold hamiltonian; fun_prop
  · unfold partition hamiltonian; fun_prop
  · exact fun W => (partition_pos W).ne'

lemma preserving_product_event_real {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (T : X × Y → Z) (hT : MeasurePreserving T (μ.prod ν) ρ)
    {E : Set Z} (hE : MeasurableSet E) :
    ρ.real E = ∫ y, μ.real {x | T (x,y) ∈ E} ∂ν := by
  let f : Z → ℝ := E.indicator 1
  have hf : Measurable f := measurable_const.indicator hE
  let F := fun p : X × Y => f (T p)
  have hF : Measurable F := hf.comp hT.measurable
  have hi : Integrable F (μ.prod ν) := by
    apply (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable
    filter_upwards [] with p
    simp only [F,f]
    by_cases hp : T p ∈ E <;> simp [hp]
  have he := integral_map (μ := μ.prod ν) hT.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq,integral_indicator_one hE,integral_prod_symm F hi] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [] with y
  have hs : MeasurableSet {x | T (x,y) ∈ E} :=
    hE.preimage (hT.measurable.comp (measurable_id.prodMk measurable_const))
  exact integral_indicator_one hs

open scoped NNReal

end

open Set MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Covariance
attribute [-instance] _root_.OAI.CriticalSK.instDecidablePredEdgeTouches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK


open Set MeasureTheory

lemma covariance_continuous (n : ℕ) : Continuous (covariance (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [covariance_eq,mean]
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul continuous_const

lemma covarianceNorm_continuous (n : ℕ) : Continuous (covarianceNorm (n := n)) := by
  unfold covarianceNorm
  have h : Continuous (fun W : Disorder n => (covariance W).toEuclideanLin.toContinuousLinearMap) := by
    exact (LinearMap.continuous_of_finiteDimensional
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap).comp (covariance_continuous n)
  exact h.norm

lemma variance_linear_quadratic {n : ℕ} (W : Disorder n) (a : EuclideanSpace ℝ (Fin n)) :
    variance W (linearObservable a) = inner ℝ a ((covariance W).toEuclideanLin a) := by
  rw [variance,mean_linearObservable]
  simp only [sub_zero,mean,linearObservable,
    EuclideanSpace.inner_eq_star_dotProduct,star_trivial,Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,covariance_eq,mean]
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma variance_linear_le_norm {n : ℕ} (W : Disorder n) (a : EuclideanSpace ℝ (Fin n)) :
    variance W (linearObservable a) ≤ covarianceNorm W*‖a‖^2 := by
  rw [variance_linear_quadratic]
  have hh := real_inner_le_norm a ((covariance W).toEuclideanLin a)
  have hn := (covariance W).toEuclideanLin.toContinuousLinearMap.le_opNorm a
  calc
    inner ℝ a ((covariance W).toEuclideanLin a) ≤ ‖a‖*‖(covariance W).toEuclideanLin a‖ := hh
    _ ≤ ‖a‖*(covarianceNorm W*‖a‖) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = covarianceNorm W*‖a‖^2 := by ring

lemma variance_linear_smallBall {n : ℕ} (W : Disorder n) (a : Fin n → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    b^2*(1-linearSmallBall W a b) ≤ variance W (linearObservable a) := by
  rw [variance,mean_linearObservable]
  simp only [sub_zero,mean]
  rw [← gibbs_sum W,linearSmallBall,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : |linearObservable a x| ≤ b
  · simp only [ite_eq_left hx,sub_self,mul_zero]
    exact mul_nonneg (gibbs_nonneg W x) (sq_nonneg _)
  · simp only [ite_eq_right hx,sub_zero]
    have hs : b^2 ≤ linearObservable a x^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hb (le_of_lt (lt_of_not_ge hx)) 2
    nlinarith [mul_le_mul_of_nonneg_left hs (gibbs_nonneg W x)]

lemma gibbsOverlap_nonneg {n : ℕ} (W : Disorder n) : 0 ≤ gibbsOverlap W := by
  unfold gibbsOverlap
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    exact mul_nonneg (mul_nonneg (gibbs_nonneg W x) (gibbs_nonneg W y)) (sq_nonneg _)


open Set MeasureTheory Filter

lemma covariance_lower_tight {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | covarianceNorm W ≤ c*(n+4:ℝ)^(2/3:ℝ)} < α := by
  obtain ⟨b,hb,hp⟩ := natural_smallBall_tight (by norm_num : (0:ℝ) < 1/2) hα
  refine ⟨b^2/2,by positivity,?_⟩
  filter_upwards [hp] with n hn
  refine lt_of_le_of_lt (measureReal_mono ?_) hn
  intro W hW u hu
  have hN := variance_linear_le_norm W u
  rw [hu,one_pow,mul_one] at hN
  have hV := variance_linear_smallBall W u (show 0 ≤ b*(n+4:ℝ)^(1/3:ℝ) by positivity)
  rw [mul_pow,third_power_square (by positivity : (0:ℝ) ≤ n+4)] at hV
  change covarianceNorm W ≤ b^2/2*(n+4:ℝ)^(2/3:ℝ) at hW
  have hP : 0 < b^2*(n+4:ℝ)^(2/3:ℝ) := by positivity
  nlinarith

lemma tight_interval_limit {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : ∀ n, X n → ℝ) (hf : ∀ n, Measurable (f n))
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (hlower : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | f n x ≤ c*s n} < α)
    (hupper : ∀ α : ℝ, 0 < α → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {x | C*s n ≤ f n x} < α)
    (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (μ n).real {x | s n/M n ≤ f n x ∧ f n x ≤ M n*s n}) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨c,hc,hl⟩ := hlower ((1-a)/2) (by linarith)
    obtain ⟨C,hC,hu⟩ := hupper ((1-a)/2) (by linarith)
    filter_upwards [hl,hu,(tendsto_atTop.mp hM (1/c)),(tendsto_atTop.mp hM C)] with n hnlo hnup hnM hnC
    let E : Set (X n) := {x | s n/M n ≤ f n x ∧ f n x ≤ M n*s n}
    have hE : MeasurableSet E := (measurableSet_le measurable_const (hf n)).inter
      (measurableSet_le (hf n) measurable_const)
    have hlow : s n/M n ≤ c*s n := by
      apply (div_le_iff₀ (hMpos n)).mpr
      have hh : 1 ≤ M n*c := (div_le_iff₀ hc).mp hnM
      nlinarith [mul_le_mul_of_nonneg_right hh (hs n).le]
    have hset : Eᶜ ⊆ {x | f n x ≤ c*s n} ∪ {x | C*s n ≤ f n x} := by
      intro x hx
      by_cases hxl : s n/M n ≤ f n x
      · right
        have hxu : M n*s n < f n x := by
          apply lt_of_not_ge
          intro hh
          exact hx ⟨hxl,hh⟩
        exact (mul_le_mul_of_nonneg_right hnC (hs n).le).trans hxu.le
      · left
        exact (lt_of_not_ge hxl).le.trans hlow
    have hbad := (measureReal_mono (μ := μ n) hset).trans (measureReal_union_le _ _)
    have hadd := measureReal_add_measureReal_compl (μ := μ n) hE
    rw [probReal_univ] at hadd
    change a < (μ n).real E
    linarith
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

theorem covariance_natural_scale (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (disorderLaw n).real {W |
      (n:ℝ)^(2/3:ℝ)/M n ≤ covarianceNorm W ∧ covarianceNorm W ≤ M n*(n:ℝ)^(2/3:ℝ)}) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  have hh := tight_interval_limit (fun n => disorderLaw (n+4)) (fun _ W => covarianceNorm W)
    (fun n => (covarianceNorm_continuous (n+4)).measurable)
    (fun n => (n+4:ℝ)^(2/3:ℝ)) (fun _ => by positivity)
    (fun _ hα => covariance_lower_tight hα) (fun _ hα => covariance_upper_tight hα)
    (fun n => M (n+4)) (fun n => hMpos (n+4)) (hM.comp (tendsto_add_atTop_nat 4))
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Rayleigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

lemma cavityOverlapCoord_abs_le_one (i : Fin n) (x y : Spin n) : |cavityOverlapCoord i x y| ≤ 1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  rw [cavityOverlapCoord,abs_div,abs_of_pos hn,div_le_one hn]
  calc
    |∑ j ∈ Finset.univ.erase i, spinValue (x j)*spinValue (y j)| ≤ ∑ j ∈ Finset.univ.erase i, |spinValue (x j)*spinValue (y j)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ)-1 := by
      simp only [abs_mul,abs_spinValue,mul_one,Finset.sum_const,nsmul_eq_mul,mul_one]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]
    _ ≤ (n:ℝ) := by linarith

lemma cavityNormalization_join (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) :
    cavityNormalization ((cavitySplit i).symm (u,v)) i =
      coshMixture (gibbs ((cavitySplit i).symm (0,v))) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) u := by
  simp only [cavityNormalization,delete_cavityJoin,mean,coshMixture,localField_cavityJoin,gaussianLinear]

lemma cavityOverlap_join (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) :
    cavityOverlap ((cavitySplit i).symm (u,v)) i =
      ∑ x, ∑ y, gibbs ((cavitySplit i).symm (0,v)) x*gibbs ((cavitySplit i).symm (0,v)) y*cavityOverlapCoord i x y^2 := by
  simp only [cavityOverlap,delete_cavityJoin,mean,Finset.mul_sum,mul_assoc]

lemma incident_variance_bound (i : Fin n) : (n:ℝ)⁻¹*((n:ℝ)-1) ≤ 1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  calc
    _ ≤ (n:ℝ)⁻¹*(n:ℝ) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hn.le)
    _ = 1 := inv_mul_cancel₀ hn.ne'

lemma incident_scaled_product (i : Fin n) (x y : Spin n) :
    (n:ℝ)⁻¹*(∑ e : Incident i, incidentCoeff i x e.val*incidentCoeff i y e.val) = cavityOverlapCoord i x y := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  rw [incident_coeff_product,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

lemma cavity_conditional_pow (i : Fin n) (v : Nonincident i → ℝ) (m : ℕ) :
    Integrable (fun u => cavityNormalization ((cavitySplit i).symm (u,v)) i^m) (incidentLaw i) ∧
    (∫ u, cavityNormalization ((cavitySplit i).symm (u,v)) i^m ∂incidentLaw i) ≤ 2*Real.exp ((m:ℝ)^2/2) := by
  have hh := coshMixture_pow_integrable_bound (n:ℝ≥0)⁻¹ (gibbs_nonneg ((cavitySplit i).symm (0,v))) (gibbs_sum _) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) (incident_coeff_square i) m
  simp only [NNReal.coe_inv,NNReal.coe_natCast] at hh
  simp_rw [cavityNormalization_join]
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (incident_variance_bound i) (sq_nonneg (m:ℝ))]

lemma cavity_conditional_variance (i : Fin n) (v : Nonincident i → ℝ) :
    Integrable (fun u => (cavityNormalization ((cavitySplit i).symm (u,v)) i-Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2))^2) (incidentLaw i) ∧
    (∫ u, (cavityNormalization ((cavitySplit i).symm (u,v)) i-Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2))^2 ∂incidentLaw i) ≤
      Real.exp 1*(Real.exp 1-1)*cavityOverlap ((cavitySplit i).symm (0,v)) i := by
  have hc (x y : Spin n) : |((n:ℝ≥0)⁻¹:ℝ)*(∑ e : Incident i, incidentCoeff i x e.val*incidentCoeff i y e.val)| ≤ 1 := by
    simpa only [NNReal.coe_inv,NNReal.coe_natCast,incident_scaled_product] using cavityOverlapCoord_abs_le_one i x y
  have hh := coshMixture_centered_integrable_bound (n:ℝ≥0)⁻¹ (gibbs_nonneg ((cavitySplit i).symm (0,v))) (gibbs_sum _) (fun (x : Spin n) (e : Incident i) => incidentCoeff i x e.val) (incident_coeff_square i) hc
  simp only [NNReal.coe_inv,NNReal.coe_natCast,incident_scaled_product] at hh
  simp_rw [← cavityNormalization_join] at hh
  rw [← cavityOverlap_join i 0 v] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (incident_variance_bound i)) (by linarith [Real.add_one_le_exp 1])) (cavityOverlap_nonneg _ i)

lemma deleteDisorder_continuous (i : Fin n) : Continuous (fun W : Disorder n => deleteDisorder W i) := by
  apply continuous_pi
  intro e
  by_cases he : e.val.1=i ∨ e.val.2=i
  · simp only [deleteDisorder,ite_eq_left he]; exact continuous_const
  · simp only [deleteDisorder,ite_eq_right he]; exact continuous_apply e

lemma localField_continuous (i : Fin n) (x : Spin n) : Continuous (fun W : Disorder n => localField W i x) := by
  unfold localField
  fun_prop

lemma cavityNormalization_continuous (i : Fin n) : Continuous (fun W : Disorder n => cavityNormalization W i) := by
  unfold cavityNormalization mean
  apply continuous_finsetSum
  intro x _
  exact ((gibbs_continuous x).comp (deleteDisorder_continuous i)).mul (Real.continuous_cosh.comp (localField_continuous i x))

lemma cavityOverlap_continuous (i : Fin n) : Continuous (fun W : Disorder n => cavityOverlap W i) := by
  unfold cavityOverlap mean
  apply continuous_finsetSum
  intro x _
  apply ((gibbs_continuous x).comp (deleteDisorder_continuous i)).mul
  apply continuous_finsetSum
  intro y _
  exact ((gibbs_continuous y).comp (deleteDisorder_continuous i)).mul continuous_const

lemma cavity_event_identity (i : Fin n) {E : Set (Disorder n)} (hE : MeasurableSet E) :
    (disorderLaw n).real E = ∫ v, (incidentLaw i).real {u | (cavitySplit i).symm (u,v) ∈ E} ∂nonincidentLaw i :=
  preserving_product_event_real _ _ _ _ (cavitySplit_preserving i).symm hE

lemma cavity_conditional_tail (i : Fin n) (v : Nonincident i → ℝ) {b : ℝ} (hb : 0 < b) (m : ℕ) :
    (incidentLaw i).real {u | b ≤ cavityNormalization ((cavitySplit i).symm (u,v)) i} ≤ 2*Real.exp ((m:ℝ)^2/2)/b^m := by
  obtain ⟨hi,hh⟩ := cavity_conditional_pow i v m
  have ht := integral_dominates_event (E := {u | b ≤ cavityNormalization ((cavitySplit i).symm (u,v)) i})
    (hi.div_const (b^m)) (fun u => div_nonneg (pow_nonneg (by linarith [cavityNormalization_ge_one ((cavitySplit i).symm (u,v)) i]) _) (pow_nonneg hb.le _))
    (fun u hu => by
      apply (le_div_iff₀ (pow_pos hb _)).mpr
      rw [one_mul]
      exact pow_le_pow_left₀ hb.le hu _)
  rw [integral_div] at ht
  exact ht.trans (div_le_div_of_nonneg_right hh (pow_nonneg hb.le _))

lemma cavity_tail (i : Fin n) {b : ℝ} (hb : 0 < b) (m : ℕ) :
    (disorderLaw n).real {W | b ≤ cavityNormalization W i} ≤ 2*Real.exp ((m:ℝ)^2/2)/b^m := by
  rw [cavity_event_identity i (measurableSet_le measurable_const (cavityNormalization_continuous i).measurable)]
  calc
    _ ≤ ∫ _v, 2*Real.exp ((m:ℝ)^2/2)/b^m ∂nonincidentLaw i :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg)) (integrable_const _) (ae_of_all _ (fun v => cavity_conditional_tail i v hb m))
    _ = _ := by simp

lemma all_cavity_tail {b : ℝ} (hb : 0 < b) (m : ℕ) :
    (disorderLaw n).real {W | ∃ i, b ≤ cavityNormalization W i} ≤ (n:ℝ)*(2*Real.exp ((m:ℝ)^2/2)/b^m) := by
  have he : {W : Disorder n | ∃ i, b ≤ cavityNormalization W i} = ⋃ i : Fin n, {W | b ≤ cavityNormalization W i} := by ext W; simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin n, (disorderLaw n).real {W | b ≤ cavityNormalization W i} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2*Real.exp ((m:ℝ)^2/2)/b^m := Finset.sum_le_sum (fun i _ => cavity_tail i hb m)
    _ = _ := by simp

lemma cavity_conditional_clipped (i : Fin n) (v : Nonincident i → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (incidentLaw i).real {u | Real.exp 1+1 < cavityNormalization ((cavitySplit i).symm (u,v)) i ∧ cavityOverlap ((cavitySplit i).symm (u,v)) i ≤ r} ≤
      Real.exp 1*(Real.exp 1-1)*r := by
  have he (u : Incident i → ℝ) : cavityOverlap ((cavitySplit i).symm (u,v)) i = cavityOverlap ((cavitySplit i).symm (0,v)) i := by
    rw [cavityOverlap_join,cavityOverlap_join]
  by_cases hR : cavityOverlap ((cavitySplit i).symm (0,v)) i ≤ r
  · obtain ⟨hi,hh⟩ := cavity_conditional_variance i v
    have hm : Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith [incident_variance_bound i])
    have ht := integral_dominates_event (E := {u | Real.exp 1+1 < cavityNormalization ((cavitySplit i).symm (u,v)) i ∧ cavityOverlap ((cavitySplit i).symm (u,v)) i ≤ r}) hi (fun _ => sq_nonneg _) (fun u hu => by
      have hz := hu.1
      nlinarith [sq_nonneg (cavityNormalization ((cavitySplit i).symm (u,v)) i-Real.exp ((n:ℝ)⁻¹*((n:ℝ)-1)/2)-1)])
    exact ht.trans (hh.trans (mul_le_mul_of_nonneg_left hR (mul_nonneg (Real.exp_pos _).le (by linarith [Real.add_one_le_exp 1]))))
  · have hset : {u | Real.exp 1+1 < cavityNormalization ((cavitySplit i).symm (u,v)) i ∧ cavityOverlap ((cavitySplit i).symm (u,v)) i ≤ r} = ∅ := by
      ext u
      simp only [mem_ofPred_eq,he,mem_empty_iff_false,iff_false,not_and]
      exact fun _ => hR
    rw [hset,measureReal_empty]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith [Real.add_one_le_exp 1])) hr

lemma cavityClipped_measurable (i : Fin n) (r : ℝ) : MeasurableSet {W : Disorder n | Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r} :=
  (measurableSet_lt measurable_const (cavityNormalization_continuous i).measurable).inter (measurableSet_le (cavityOverlap_continuous i).measurable measurable_const)

lemma cavity_clipped (i : Fin n) {r : ℝ} (hr : 0 ≤ r) :
    (disorderLaw n).real {W | Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r} ≤ Real.exp 1*(Real.exp 1-1)*r := by
  rw [cavity_event_identity i (cavityClipped_measurable i r)]
  calc
    _ ≤ ∫ _v, Real.exp 1*(Real.exp 1-1)*r ∂nonincidentLaw i :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg)) (integrable_const _) (ae_of_all _ (fun v => cavity_conditional_clipped i v hr))
    _ = _ := by simp

lemma cavityClippedCount_nonneg (W : Disorder n) (r : ℝ) : 0 ≤ cavityClippedCount W r := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

lemma cavityClippedCount_integrable (r : ℝ) : Integrable (fun W : Disorder n => cavityClippedCount W r) (disorderLaw n) := by
  unfold cavityClippedCount
  apply integrable_finsetSum
  intro i _
  refine ((integrable_const (μ := disorderLaw n) (1:ℝ)).indicator (cavityClipped_measurable i r)).congr (ae_of_all _ ?_)
  intro W
  by_cases hW : Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r <;> simp [hW]

lemma cavityClippedCount_expectation {r : ℝ} (hr : 0 ≤ r) :
    (∫ W, cavityClippedCount W r ∂disorderLaw n) ≤ (n:ℝ)*(Real.exp 1*(Real.exp 1-1)*r) := by
  unfold cavityClippedCount
  rw [integral_finsetSum]
  · calc
      _ = ∑ i : Fin n, (disorderLaw n).real {W | Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r} := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Set.indicator, mem_ofPred_eq, Pi.one_apply] using integral_indicator_one (μ := disorderLaw n) (cavityClipped_measurable i r)
      _ ≤ ∑ _i : Fin n, Real.exp 1*(Real.exp 1-1)*r := Finset.sum_le_sum (fun i _ => cavity_clipped i hr)
      _ = _ := by simp
  · intro i _
    refine ((integrable_const (μ := disorderLaw n) (1:ℝ)).indicator (cavityClipped_measurable i r)).congr (ae_of_all _ ?_)
    intro W
    by_cases hW : Real.exp 1+1 < cavityNormalization W i ∧ cavityOverlap W i ≤ r <;> simp [hW]

lemma cavityClippedCount_tail {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) :
    (disorderLaw n).real {W | b ≤ cavityClippedCount W r} ≤ (n:ℝ)*(Real.exp 1*(Real.exp 1-1)*r)/b := by
  have ht := integral_dominates_event (μ := disorderLaw n) (E := {W | b ≤ cavityClippedCount W r}) ((cavityClippedCount_integrable r).div_const b)
    (fun W => div_nonneg (cavityClippedCount_nonneg W r) hb.le) (fun W hW => (le_div_iff₀ hb).mpr (by simpa using hW))
  rw [integral_div] at ht
  exact ht.trans (div_le_div_of_nonneg_right (cavityClippedCount_expectation hr) hb.le)

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma variance_linear_nonneg (a : Fin n → ℝ) : 0 ≤ variance W (linearObservable a) := mean_nonneg _ (fun _ => sq_nonneg _)

lemma variance_linear_norm_bound (a : Fin n → ℝ) : variance W (linearObservable a) ≤ covarianceNorm W*(∑ i, a i^2) := by
  have hh := variance_linear_le_norm W (WithLp.toLp 2 a)
  rwa [EuclideanSpace.real_norm_sq_eq] at hh

lemma linear_dirichlet_coeff_bound (A : Finset (Fin n)) (a : Fin n → ℝ) {B : ℝ} (_hB : 0 ≤ B)
    (hz : ∀ i ∈ A, cavityNormalization W i ≤ B) :
    (∑ i ∈ A, a i^2) ≤ B^2*dirichlet W (linearObservable a) := by
  have ht (i : Fin n) (hi : i ∈ A) : a i^2 ≤ B^2*(alphaSite W i*a i^2) := by
    have hZ := cavityNormalization_ge_one W i
    have hα := alphaSite_pos W i
    have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ cavityNormalization W i) (hz i hi) 2
    have hh := alphaSite_normalization W i
    have hmul := mul_le_mul_of_nonneg_left hsq hα.le
    have hn : 1 ≤ B^2*alphaSite W i := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hn (sq_nonneg (a i))]
  calc
    _ ≤ ∑ i ∈ A, B^2*(alphaSite W i*a i^2) := Finset.sum_le_sum ht
    _ = B^2*(∑ i ∈ A, alphaSite W i*a i^2) := by rw [Finset.mul_sum]
    _ ≤ B^2*(∑ i : Fin n, alphaSite W i*a i^2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => mul_nonneg (alphaSite_pos W i).le (sq_nonneg _))
    _ = _ := by rw [dirichlet_linear_eq]

lemma restrictCoeff_sum_sq (A : Finset (Fin n)) (a : Fin n → ℝ) :
    (∑ i : Fin n, restrictCoeff A a i^2) = ∑ i ∈ A, a i^2 := by
  simp [restrictCoeff,ite_pow,Finset.sum_ite_mem]

lemma restrictCoeff_linear (A : Finset (Fin n)) (a : Fin n → ℝ) (x : Spin n) :
    linearObservable (restrictCoeff A a) x = ∑ i ∈ A, a i*spinValue (x i) := by
  simp [linearObservable,restrictCoeff,ite_mul,Finset.sum_ite_mem]

lemma restrictCoeff_linear_sq (A : Finset (Fin n)) (a : Fin n → ℝ) (x : Spin n) :
    linearObservable (restrictCoeff A a) x^2 ≤ (A.card:ℝ)*(∑ i ∈ A, a i^2) := by
  rw [restrictCoeff_linear]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq A a (fun i => spinValue (x i))
  simp only [spinValue_sq,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  nlinarith

lemma variance_linear_split_bound (A : Finset (Fin n)) (a : Fin n → ℝ) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hzG : ∀ i ∈ A, cavityNormalization W i ≤ B)
    (hzB : ∀ i ∈ Aᶜ, cavityNormalization W i ≤ K) :
    variance W (linearObservable a) ≤
      (2*B^2*covarianceNorm W+2*(Aᶜ.card:ℝ)*K^2)*dirichlet W (linearObservable a) := by
  have hsplit (x : Spin n) : linearObservable a x = linearObservable (restrictCoeff A a) x+linearObservable (restrictCoeff Aᶜ a) x := by
    rw [restrictCoeff_linear,restrictCoeff_linear,Finset.sum_add_sum_compl]
    rfl
  have hv : variance W (linearObservable a) ≤ 2*variance W (linearObservable (restrictCoeff A a))+2*variance W (linearObservable (restrictCoeff Aᶜ a)) := by
    simp only [variance,mean_linearObservable,sub_zero]
    rw [← mean_const_mul,← mean_const_mul,← mean_add]
    apply mean_mono
    intro x
    rw [hsplit]
    nlinarith [sq_nonneg (linearObservable (restrictCoeff A a) x-linearObservable (restrictCoeff Aᶜ a) x)]
  have hG := variance_linear_norm_bound W (restrictCoeff A a)
  rw [restrictCoeff_sum_sq] at hG
  have hGB := linear_dirichlet_coeff_bound W A a hB hzG
  have hBC := linear_dirichlet_coeff_bound W Aᶜ a hK hzB
  have hVB : variance W (linearObservable (restrictCoeff Aᶜ a)) ≤ (Aᶜ.card:ℝ)*(∑ i ∈ Aᶜ, a i^2) := by
    rw [variance,mean_linearObservable]
    simp only [sub_zero]
    exact (mean_mono W (restrictCoeff_linear_sq Aᶜ a)).trans_eq (mean_const _ _)
  have hN : 0 ≤ covarianceNorm W := norm_nonneg _
  have hC : 0 ≤ (Aᶜ.card:ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hGB hN,mul_le_mul_of_nonneg_left hBC hC]

lemma linear_ratio_global_bound (a : Fin n → ℝ) (ha : a ≠ 0) :
    variance W (linearObservable a)/dirichlet W (linearObservable a) ≤
      covarianceNorm W*(∑ i : Fin n, cavityNormalization W i)^2 := by
  let B := ∑ i : Fin n, cavityNormalization W i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => by linarith [cavityNormalization_ge_one W i]
  have hZ (i : Fin n) (_ : i ∈ Finset.univ) : cavityNormalization W i ≤ B :=
    Finset.single_le_sum (fun j _ => by linarith [cavityNormalization_ge_one W j]) (Finset.mem_univ i)
  have hd := linear_dirichlet_coeff_bound W Finset.univ a hB hZ
  have hV := variance_linear_norm_bound W a
  apply (div_le_iff₀ (dirichlet_linear_pos W ha)).mpr
  have hN : 0 ≤ covarianceNorm W := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hd hN]

lemma linear_ratios_bdd : BddAbove {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧ r = variance W (linearObservable a)/dirichlet W (linearObservable a)} := by
  refine ⟨covarianceNorm W*(∑ i : Fin n, cavityNormalization W i)^2,?_⟩
  rintro r ⟨a,ha,rfl⟩
  exact linear_ratio_global_bound W a ha

lemma linear_ratios_nonempty (hn : 0 < n) : Set.Nonempty {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧ r = variance W (linearObservable a)/dirichlet W (linearObservable a)} := by
  refine ⟨_,(fun _ => 1),?_,rfl⟩
  intro hh
  have he := congrFun hh ⟨0,hn⟩
  norm_num at he

lemma linear_ratio_le (a : Fin n → ℝ) (ha : a ≠ 0) :
    variance W (linearObservable a)/dirichlet W (linearObservable a) ≤ linearRayleigh W :=
  le_csSup (linear_ratios_bdd W) ⟨a,ha,rfl⟩

lemma linearRayleigh_split_bound (hn : 0 < n) (A : Finset (Fin n)) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hzG : ∀ i ∈ A, cavityNormalization W i ≤ B)
    (hzB : ∀ i ∈ Aᶜ, cavityNormalization W i ≤ K) :
    linearRayleigh W ≤ 2*B^2*covarianceNorm W+2*(Aᶜ.card:ℝ)*K^2 := by
  apply csSup_le (linear_ratios_nonempty W hn)
  rintro r ⟨a,ha,rfl⟩
  exact (div_le_iff₀ (dirichlet_linear_pos W ha)).mpr (variance_linear_split_bound W A a hB hK hzG hzB)

lemma linearRayleigh_smallBall (a : Fin n → ℝ) (ha : ∑ i, a i^2 = 1) {b : ℝ} (hb : 0 ≤ b) :
    b^2*(1-linearSmallBall W a b) ≤ linearRayleigh W := by
  have hane : a ≠ 0 := by intro hh; simp only [hh,Pi.zero_apply,zero_pow (by norm_num : (2:ℕ) ≠ 0),Finset.sum_const_zero] at ha; norm_num at ha
  have hd := dirichlet_linear_le W a
  rw [ha] at hd
  have hdp := dirichlet_linear_pos W hane
  have hV := variance_linear_nonneg W a
  have hr : variance W (linearObservable a) ≤ variance W (linearObservable a)/dirichlet W (linearObservable a) :=
    (le_div_iff₀ hdp).mpr (by nlinarith)
  exact (variance_linear_smallBall W a hb).trans (hr.trans (linear_ratio_le W a hane))

end

section

open Set Filter MeasureTheory

variable {n : ℕ}

lemma variance_linear_continuous (a : Fin n → ℝ) : Continuous (fun W : Disorder n => variance W (linearObservable a)) := by
  simp_rw [variance,mean_linearObservable]
  simp only [sub_zero,mean]
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul continuous_const

lemma alphaSite_continuous (i : Fin n) : Continuous (fun W : Disorder n => alphaSite W i) := by
  unfold alphaSite mean
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul (((Real.continuous_cosh.comp (localField_continuous i x)).inv₀ (fun _ => (Real.cosh_pos _).ne')).pow 2)

lemma dirichlet_linear_continuous (a : Fin n → ℝ) : Continuous (fun W : Disorder n => dirichlet W (linearObservable a)) := by
  simp only [dirichlet_linear_eq]
  apply continuous_finsetSum
  intro i _
  exact (alphaSite_continuous i).mul continuous_const

lemma linear_ratio_continuous (a : Fin n → ℝ) (ha : a ≠ 0) :
    Continuous (fun W : Disorder n => variance W (linearObservable a)/dirichlet W (linearObservable a)) :=
  (variance_linear_continuous a).div (dirichlet_linear_continuous a) (fun W => (dirichlet_linear_pos W ha).ne')

lemma linearRayleigh_eq_iSup (W : Disorder n) : linearRayleigh W =
    ⨆ a : {a : Fin n → ℝ // a ≠ 0}, variance W (linearObservable a.val)/dirichlet W (linearObservable a.val) := by
  change sSup _ = sSup _
  congr 1
  ext r
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨a,ha⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a.val,a.property,rfl⟩

lemma linearRayleigh_measurable (n : ℕ) : Measurable (linearRayleigh (n := n)) := by
  have hh : LowerSemicontinuous (linearRayleigh (n := n)) := by
    change LowerSemicontinuous (fun W : Disorder n => linearRayleigh W)
    simp_rw [linearRayleigh_eq_iSup]
    apply lowerSemicontinuous_ciSup
    · intro W
      refine ⟨covarianceNorm W*(∑ i : Fin n, cavityNormalization W i)^2,?_⟩
      rintro r ⟨a,rfl⟩
      exact linear_ratio_global_bound W a.val a.property
    · intro a
      exact (linear_ratio_continuous a.val a.property).lowerSemicontinuous
  exact hh.measurable

end

open Set Filter MeasureTheory

lemma shift_rpow_neg_tendsto {p : ℝ} (hp : 0 < p) : Tendsto (fun n : ℕ => (n+4:ℝ)^(-p)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hp).comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 4))
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using hh

lemma cavity_max_rate_identity {x : ℝ} (hx : 0 < x) :
    x*(2*Real.exp 20000/(x^(1/100:ℝ))^200) = (2*Real.exp 20000)*x^(-1:ℝ) := by
  rw [← Real.rpow_mul_natCast hx.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

lemma cavity_count_rate_identity {x : ℝ} (hx : 0 < x) :
    x*(Real.exp 1*(Real.exp 1-1)*x^(-1/2:ℝ))/x^(3/5:ℝ) = (Real.exp 1*(Real.exp 1-1))*x^(-1/10:ℝ) := by
  calc
    _ = (Real.exp 1*(Real.exp 1-1))*(x^((1:ℝ))*x^(-1/2:ℝ)/x^(3/5:ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hx,← Real.rpow_sub hx]; congr 2; norm_num

lemma cavity_overlap_rate_identity {x : ℝ} (hx : 0 < x) :
    2*(x^(1/100:ℝ))^2*(x^(-3/5:ℝ)+x⁻¹^2)/x^(-1/2:ℝ) =
      2*(x^(-2/25:ℝ)+x^(-37/25:ℝ)) := by
  have he : x⁻¹^2 = x^(-2:ℝ) := by rw [Real.rpow_neg hx.le,Real.rpow_two,inv_pow]
  rw [he,← Real.rpow_mul_natCast hx.le]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = 2*((x^(1/100*2:ℝ)*x^(-3/5:ℝ)/x^(-1/2:ℝ))+(x^(1/100*2:ℝ)*x^(-2:ℝ)/x^(-1/2:ℝ))) := by ring_nf
    _ = _ := by rw [← Real.rpow_add hx,← Real.rpow_sub hx,← Real.rpow_add hx,← Real.rpow_sub hx]; congr 2 <;> norm_num

lemma cavity_overlap_rate_eventually : ∀ᶠ n : ℕ in atTop,
    2*((n+4:ℝ)^(1/100:ℝ))^2*((n+4:ℝ)^(-3/5:ℝ)+(n+4:ℝ)⁻¹^2) ≤ (n+4:ℝ)^(-1/2:ℝ) := by
  have hh := ((shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<2/25)).add (shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<37/25))).const_mul 2
  simp only [mul_zero,add_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  apply (div_le_one (by positivity : (0:ℝ)<(n+4:ℝ)^(-1/2:ℝ))).mp
  rw [cavity_overlap_rate_identity (by positivity)]
  simpa only [neg_div] using hn.le

lemma rayleigh_error_rate_identity {x : ℝ} (hx : 0 < x) :
    (x^(3/5:ℝ)*(x^(1/100:ℝ))^2)/x^(2/3:ℝ) = x^(-7/150:ℝ) := by
  rw [← Real.rpow_mul_natCast hx.le,← Real.rpow_add hx,← Real.rpow_sub hx]
  norm_num

lemma rayleigh_error_rate_eventually : ∀ᶠ n : ℕ in atTop,
    (n+4:ℝ)^(3/5:ℝ)*((n+4:ℝ)^(1/100:ℝ))^2 ≤ (n+4:ℝ)^(2/3:ℝ) := by
  filter_upwards [(shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<7/150)).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  apply (div_le_one (by positivity : (0:ℝ)<(n+4:ℝ)^(2/3:ℝ))).mp
  rw [rayleigh_error_rate_identity (by positivity)]
  simpa only [neg_div] using hn.le

lemma cavity_max_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | ∃ i, (n+4:ℝ)^(1/100:ℝ) ≤ cavityNormalization W i}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (g := fun n : ℕ => (2*Real.exp 20000)*(n+4:ℝ)^(-1:ℝ))
  · intro n
    have hh := all_cavity_tail (n := n+4) (by positivity : (0:ℝ)<(n+4:ℝ)^(1/100:ℝ)) 200
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
    rwa [cavity_max_rate_identity (by positivity)] at hh
  · simpa using (shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<1)).const_mul (2*Real.exp 20000)

lemma cavity_count_tail_zero : Tendsto (fun n : ℕ => (disorderLaw (n+4)).real
    {W | (n+4:ℝ)^(3/5:ℝ) ≤ cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ))}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (g := fun n : ℕ => (Real.exp 1*(Real.exp 1-1))*(n+4:ℝ)^(-1/10:ℝ))
  · intro n
    have hh := cavityClippedCount_tail (n := n+4) (by positivity : (0:ℝ)≤(n+4:ℝ)^(-1/2:ℝ)) (by positivity : (0:ℝ)<(n+4:ℝ)^(3/5:ℝ))
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
    simp only [← neg_div] at hh
    rwa [cavity_count_rate_identity (by positivity)] at hh
  · simpa only [mul_zero,neg_div] using (shift_rpow_neg_tendsto (by norm_num : (0:ℝ)<1/10)).const_mul (Real.exp 1*(Real.exp 1-1))

lemma rayleigh_cavity_good_bound (n : ℕ) (W : Disorder (n+4))
    (hrate : 2*((n+4:ℝ)^(1/100:ℝ))^2*((n+4:ℝ)^(-3/5:ℝ)+(n+4:ℝ)⁻¹^2) ≤ (n+4:ℝ)^(-1/2:ℝ))
    (herr : (n+4:ℝ)^(3/5:ℝ)*((n+4:ℝ)^(1/100:ℝ))^2 ≤ (n+4:ℝ)^(2/3:ℝ))
    (hZ : ∀ i, cavityNormalization W i < (n+4:ℝ)^(1/100:ℝ))
    (hQ : gibbsOverlap W < (n+4:ℝ)^(-3/5:ℝ))
    (hC : cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ)) < (n+4:ℝ)^(3/5:ℝ)) :
    linearRayleigh W ≤ 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) := by
  classical
  have hR (i : Fin (n+4)) : cavityOverlap W i ≤ (n+4:ℝ)^(-1/2:ℝ) := by
    have hh := cavityOverlap_compare W i
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hh
    refine hh.trans (le_trans ?_ hrate)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [cavityNormalization_ge_one W i]) (hZ i).le 2) (by norm_num)
    · exact add_le_add hQ.le le_rfl
    · exact add_nonneg (gibbsOverlap_nonneg W) (sq_nonneg _)
    · positivity
  let A : Finset (Fin (n+4)) := Finset.univ.filter (fun i => cavityNormalization W i ≤ Real.exp 1+1)
  have hcard : (Aᶜ.card:ℝ) = cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ)) := by
    rw [cavityClippedCount]
    have he (i : Fin (n+4)) : i ∈ Aᶜ ↔ Real.exp 1+1 < cavityNormalization W i := by simp [A]
    calc
      _ = ∑ i : Fin (n+4), if i ∈ Aᶜ then (1:ℝ) else 0 := by rw [← Finset.sum_filter]; simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,mul_one]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [he,hR i,and_true]
  have hb := linearRayleigh_split_bound W (by omega : 0<n+4) A
    (by positivity : (0:ℝ)≤Real.exp 1+1) (by positivity : (0:ℝ)≤(n+4:ℝ)^(1/100:ℝ))
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun i _ => (hZ i).le)
  rw [hcard] at hb
  have hm := mul_le_mul_of_nonneg_right hC.le (sq_nonneg ((n+4:ℝ)^(1/100:ℝ)))
  linarith

lemma linearRayleigh_cavity_comparison : ∀ α : ℝ, 0 < α → ∀ᶠ n : ℕ in atTop,
    (disorderLaw (n+4)).real {W | 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W} < α := by
  intro α hα
  filter_upwards [cavity_overlap_rate_eventually,rayleigh_error_rate_eventually,
    cavity_max_tail_zero.eventually (gt_mem_nhds (show 0<α/3 by positivity)),
    cavity_overlap_tail_zero.eventually (gt_mem_nhds (show 0<α/3 by positivity)),
    cavity_count_tail_zero.eventually (gt_mem_nhds (show 0<α/3 by positivity))] with n hr he hZ hQ hC
  have hs : {W : Disorder (n+4) | 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W} ⊆
      ({W | ∃ i, (n+4:ℝ)^(1/100:ℝ) ≤ cavityNormalization W i} ∪ {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}) ∪
      {W | (n+4:ℝ)^(3/5:ℝ) ≤ cavityClippedCount W ((n+4:ℝ)^(-1/2:ℝ))} := by
    intro W hW
    by_contra hh
    simp only [mem_union,mem_ofPred_eq,not_or,not_exists,not_le] at hh
    exact (not_lt_of_ge (rayleigh_cavity_good_bound n W hr he hh.1.1 hh.1.2 hh.2)) hW
  have hp := (measureReal_mono (μ := disorderLaw (n+4)) hs).trans (measureReal_union_le _ _)
  have hp' := measureReal_union_le (μ := disorderLaw (n+4))
    {W | ∃ i, (n+4:ℝ)^(1/100:ℝ) ≤ cavityNormalization W i} {W | (n+4:ℝ)^(-3/5:ℝ) ≤ gibbsOverlap W}
  linarith

lemma linearRayleigh_lower_tight {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | linearRayleigh W ≤ c*(n+4:ℝ)^(2/3:ℝ)} < α := by
  obtain ⟨b,hb,hp⟩ := natural_smallBall_tight (by norm_num : (0:ℝ) < 1/2) hα
  refine ⟨b^2/2,by positivity,?_⟩
  filter_upwards [hp] with n hn
  refine lt_of_le_of_lt (measureReal_mono ?_) hn
  intro W hW u hu
  have husq : ∑ i, u i^2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq u,hu,one_pow]
  have hV := linearRayleigh_smallBall W (fun i => u i) husq (show 0 ≤ b*(n+4:ℝ)^(1/3:ℝ) by positivity)
  rw [mul_pow,third_power_square (by positivity : (0:ℝ) ≤ n+4)] at hV
  change linearRayleigh W ≤ b^2/2*(n+4:ℝ)^(2/3:ℝ) at hW
  have hP : 0 < b^2*(n+4:ℝ)^(2/3:ℝ) := by positivity
  nlinarith

lemma linearRayleigh_upper_tight {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (disorderLaw (n+4)).real
      {W | C*(n+4:ℝ)^(2/3:ℝ) ≤ linearRayleigh W} < α := by
  obtain ⟨K,hK,hp⟩ := covariance_upper_tight (show 0<α/2 by positivity)
  let C := 2*(Real.exp 1+1)^2*K+3
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hp,linearRayleigh_cavity_comparison (α/2) (by positivity)] with n hn hc
  have hs : {W : Disorder (n+4) | C*(n+4:ℝ)^(2/3:ℝ) ≤ linearRayleigh W} ⊆
      {W | K*(n+4:ℝ)^(2/3:ℝ) ≤ covarianceNorm W} ∪
      {W | 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W} := by
    intro W hW
    by_cases hh : K*(n+4:ℝ)^(2/3:ℝ) ≤ covarianceNorm W
    · exact Or.inl hh
    · right
      change C*(n+4:ℝ)^(2/3:ℝ) ≤ linearRayleigh W at hW
      have hN := lt_of_not_ge hh
      have hmul := mul_lt_mul_of_pos_left hN (show 0<2*(Real.exp 1+1)^2 by positivity)
      dsimp only [C] at hW
      have hpN : 0<(n+4:ℝ)^(2/3:ℝ) := by positivity
      change 2*(Real.exp 1+1)^2*covarianceNorm W+2*(n+4:ℝ)^(2/3:ℝ) < linearRayleigh W
      nlinarith
  have hb := (measureReal_mono (μ := disorderLaw (n+4)) hs).trans (measureReal_union_le _ _)
  linarith

theorem linearRayleigh_natural_scale (M : ℕ → ℝ) (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n => (disorderLaw n).real {W |
      (n:ℝ)^(2/3:ℝ)/M n ≤ linearRayleigh W ∧ linearRayleigh W ≤ M n*(n:ℝ)^(2/3:ℝ)}) atTop (𝓝 1) := by
  apply (tendsto_add_atTop_iff_nat 4).mp
  have hh := tight_interval_limit (fun n => disorderLaw (n+4)) (fun _ W => linearRayleigh W)
    (fun n => linearRayleigh_measurable (n+4))
    (fun n => (n+4:ℝ)^(2/3:ℝ)) (fun _ => by positivity)
    (fun _ hα => linearRayleigh_lower_tight hα) (fun _ hα => linearRayleigh_upper_tight hα)
    (fun n => M (n+4)) (fun n => hMpos (n+4)) (hM.comp (tendsto_add_atTop_nat 4))
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

lemma probability_intersection_tendsto_one {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (A B : ∀ n, Set (X n)) (_hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hpA : Tendsto (fun n => (μ n).real (A n)) atTop (𝓝 1))
    (hpB : Tendsto (fun n => (μ n).real (B n)) atTop (𝓝 1)) :
    Tendsto (fun n => (μ n).real (A n ∩ B n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => (μ n).real (A n)+(μ n).real (B n)-1) (h := fun _ => (1:ℝ))
  · simpa using (hpA.add hpB).sub_const 1
  · exact tendsto_const_nhds
  · intro n
    have hadd := measureReal_union_add_inter (μ := μ n) (s := A n) (hB n)
    have hle : (μ n).real (A n ∪ B n) ≤ 1 := measureReal_le_one
    linarith
  · exact fun _ => measureReal_le_one

theorem covariance_and_linear_tests_oai (M : ℕ → ℝ)
    (hMpos : ∀ n, 0 < M n) (hM : Tendsto M atTop atTop) :
    Tendsto (fun n : ℕ => (disorderLaw n {W |
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ covarianceNorm W ∧
      covarianceNorm W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3) ∧
      (n : ℝ) ^ ((2 : ℝ) / 3) / M n ≤ linearRayleigh W ∧
      linearRayleigh W ≤ M n * (n : ℝ) ^ ((2 : ℝ) / 3)}).toReal) atTop (𝓝 1) := by
  have hh := probability_intersection_tendsto_one disorderLaw
    (fun n => {W | (n:ℝ)^(2/3:ℝ)/M n ≤ covarianceNorm W ∧ covarianceNorm W ≤ M n*(n:ℝ)^(2/3:ℝ)})
    (fun n => {W | (n:ℝ)^(2/3:ℝ)/M n ≤ linearRayleigh W ∧ linearRayleigh W ≤ M n*(n:ℝ)^(2/3:ℝ)})
    (fun n => (measurableSet_le measurable_const (covarianceNorm_continuous n).measurable).inter (measurableSet_le (covarianceNorm_continuous n).measurable measurable_const))
    (fun n => (measurableSet_le measurable_const (linearRayleigh_measurable n)).inter (measurableSet_le (linearRayleigh_measurable n) measurable_const))
    (covariance_natural_scale M hMpos hM) (linearRayleigh_natural_scale M hMpos hM)
  simpa only [Set.inter_def,Set.mem_ofPred_eq,and_assoc,Measure.real] using hh

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.covariance_and_linear_tests_oai := @OAI.CriticalSK.covariance_and_linear_tests_oai
