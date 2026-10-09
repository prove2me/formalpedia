-- Prove2me | solution 1 for OAI.Erdos3.CylinderRemovalChain.kernel_total_pairing_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:53.087893+00:00
-- url     : https://prove2.me/submissions/8e75a3ae-476e-4b30-ac7f-48617dedc155

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_productKernel_conditioning_shell_of_truncated

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedListError
namespace OAI

section

namespace Erdos3

theorem list_weighted_error_sum {α : Type*} (xs : List α) (P m e : α → ℝ) (C : ℝ)
    (h : ∀ x ∈ xs, P x ≤ C * m x + e x) :
    (xs.map P).sum ≤ C * (xs.map m).sum + (xs.map e).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    nlinarith

theorem list_weighted_error_sum_le {α : Type*} (xs : List α) (P m e : α → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hm : (xs.map m).sum ≤ 1) (h : ∀ x ∈ xs, P x ≤ C * m x + e x) :
    (xs.map P).sum ≤ C + (xs.map e).sum := by
  have hs := list_weighted_error_sum xs P m e C h
  have hc := mul_le_mul_of_nonneg_left hm hC
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricSpectralBudgets
namespace OAI

section

namespace Erdos3

theorem geometric_tail_after_cutoff {ε P κ B : ℝ} {r : ℕ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hB0 : 0 ≤ B) (hB : B ≤ Real.exp P)
    (hr : CyclicCrootSisask.spectralIterations ε P ≤ r) :
    κ ^ r * B ≤ ε / 16 := by
  have hp : κ ^ r ≤ (1 / 2 : ℝ) ^ CyclicCrootSisask.spectralIterations ε P :=
    (pow_le_pow_left₀ hκ0 hκhalf r).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hr)
  exact (mul_le_mul hp hB hB0 (by positivity)).trans
    (CyclicCrootSisask.half_pow_spectralIterations_mul_exp_le hε)

theorem geometric_shell_after_cutoff {ε P κ B : ℝ} {i j b : ℕ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hB0 : 0 ≤ B) (hB : B ≤ Real.exp P) (hij : i ≤ j)
    (hb : j + CyclicCrootSisask.spectralIterations ε P ≤ b) :
    κ ^ (b - i) * B ≤ ε / 16 := by
  apply geometric_tail_after_cutoff hε hκ0 hκhalf hB0 hB
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.DependentShellBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem list_dependent_shell_sum_le {α : Type*} (xs : List α)
    (β : α → Type*) [∀ x, Fintype (β x)] (size : α → ℕ)
    (E B : ∀ x, β x → ℝ) {κ : ℝ} {j b : ℕ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsize : ∀ x ∈ xs, size x ≤ j) (hB : ∀ x ∈ xs, ∀ y, 0 ≤ B x y)
    (hE : ∀ x ∈ xs, ∀ y, E x y ≤ κ ^ (b - size x) * B x y) :
    (xs.map (fun x => ∑ y, E x y)).sum ≤
      κ ^ (b - j) * (xs.map (fun x => ∑ y, B x y)).sum := by
  have h := list_weighted_error_sum xs (fun x => ∑ y, E x y)
    (fun x => ∑ y, B x y) (fun _ => 0) (κ ^ (b - j)) (by
      intro x hx
      have hp : κ ^ (b - size x) ≤ κ ^ (b - j) :=
        pow_le_pow_of_le_one hκ0 hκ1 (by have := hsize x hx; omega)
      have hs : (∑ y, E x y) ≤ ∑ y, κ ^ (b - j) * B x y :=
        Finset.sum_le_sum (fun y _ => (hE x hx y).trans
          (mul_le_mul_of_nonneg_right hp (hB x hx y)))
      simpa only [← Finset.mul_sum, add_zero] using hs)
  simpa using h

theorem list_dependent_shell_sum_after_cutoff {α : Type*} (xs : List α)
    (β : α → Type*) [∀ x, Fintype (β x)] (size : α → ℕ)
    (E B : ∀ x, β x → ℝ) {ε P κ : ℝ} {j b : ℕ}
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hsize : ∀ x ∈ xs, size x ≤ j) (hB : ∀ x ∈ xs, ∀ y, 0 ≤ B x y)
    (hE : ∀ x ∈ xs, ∀ y, E x y ≤ κ ^ (b - size x) * B x y)
    (hbudget : (xs.map (fun x => ∑ y, B x y)).sum ≤ Real.exp P)
    (hb : j + CyclicCrootSisask.spectralIterations ε P ≤ b) :
    (xs.map (fun x => ∑ y, E x y)).sum ≤ ε / 16 := by
  have hs := list_dependent_shell_sum_le xs β size E B hκ0 (by linarith) hsize hB hE
  exact (hs.trans (mul_le_mul_of_nonneg_left hbudget (pow_nonneg hκ0 _))).trans
    (geometric_shell_after_cutoff hε hκ0 hκhalf (Real.exp_pos P).le le_rfl le_rfl hb)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedCoreBudget
namespace OAI

section

namespace Erdos3

theorem normalized_core_error_budget {ξ P κ A B M N : ℝ} {r : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hMN : M * N ≤ Real.exp P)
    (hr : CyclicCrootSisask.spectralIterations ξ P ≤ r)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) :
    κ * A ^ 2 * B ^ 2 ≤ 1 / 2 ∧
      4 * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N) ≤ ξ := by
  have ht := geometric_tail_after_cutoff hξ hκ0 hκhalf (mul_nonneg hM hN) hMN hr
  rw [← mul_assoc] at ht
  constructor <;> nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductSectionSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [DecidableEq I] {X : I → Type*}

theorem productCoordinateMix_empty (x y : ∀ i, X i) :
    productCoordinateMix ∅ x y = y := by
  funext i
  simp [productCoordinateMix]

theorem productCoordinateMix_comp (S T : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix S x y) z =
      productCoordinateMix (S ∩ T) x (productCoordinateMix T y z) := by
  funext i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [productCoordinateMix, hs, ht]

theorem productCoordinateMix_left (S : Finset I) (x y z : ∀ i, X i) :
    productCoordinateMix S (productCoordinateMix S x y) z = productCoordinateMix S x z := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

variable [Fintype I] [∀ i, Fintype (X i)]

theorem productCoordinateMix_weight (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (x y : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S x y) *
      (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix S y x) =
        (FiniteProbabilityWeights.pi μ).weight x * (FiniteProbabilityWeights.pi μ).weight y := by
  change (∏ i, (μ i).weight (productCoordinateMix S x y i)) *
      (∏ i, (μ i).weight (productCoordinateMix S y x i)) =
    (∏ i, (μ i).weight (x i)) * (∏ i, (μ i).weight (y i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi, mul_comm]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] (law : FiniteProbabilityWeights I)
variable (P : I → Prop) (hP : ∀ i, P i ↔ 0 < law.weight i)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

variable {Ω R : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω) (F : Ω → R)

theorem fiberMean_le_mul_mass (f : Ω → ℝ) (M : ℝ) (hf : ∀ z, f z ≤ M) (y : R) :
    p.fiberMean F y f ≤ M * p.fiberMean F y (fun _ => 1) := by
  classical
  unfold fiberMean
  rw [← p.mean_const_mul]
  apply p.mean_mono
  intro z
  by_cases hz : F z = y
  · simpa only [hz, ite_true, mul_one] using hf z
  · simp only [hz, ite_false, mul_zero, le_refl]

theorem fiberMean_zero_of_mass_zero (f : Ω → ℝ) (M : ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R)
    (hy : p.fiberMean F y (fun _ => 1) = 0) : p.fiberMean F y f = 0 := by
  have h0 := p.fiberMean_nonneg F y f (fun z => (hf z).1)
  have h1 := p.fiberMean_le_mul_mass F f M (fun z => (hf z).2) y
  rw [hy, mul_zero] at h1
  exact le_antisymm h1 h0

theorem fiberTest_bounds (f : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R) :
    0 ≤ p.fiberTest F f y ∧ p.fiberTest F f y ≤ M := by
  have hmass := p.fiberMean_nonneg F y (fun _ => 1) (fun _ => zero_le_one)
  constructor
  · exact div_nonneg (p.fiberMean_nonneg F y f (fun z => (hf z).1)) hmass
  · by_cases hy : p.fiberMean F y (fun _ => 1) = 0
    · simpa only [fiberTest, hy, div_zero] using hM
    · have hp : 0 < p.fiberMean F y (fun _ => 1) := lt_of_le_of_ne hmass (Ne.symm hy)
      exact (div_le_iff₀ hp).mpr (p.fiberMean_le_mul_mass F f M (fun z => (hf z).2) y)

theorem mass_mul_fiberTest (f : Ω → ℝ) (M : ℝ) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R) :
    p.fiberMean F y (fun _ => 1) * p.fiberTest F f y = p.fiberMean F y f := by
  by_cases hy : p.fiberMean F y (fun _ => 1) = 0
  · rw [hy, zero_mul, p.fiberMean_zero_of_mass_zero F f M hf y hy]
  · unfold fiberTest
    field_simp

end Erdos3.FiniteProbabilityWeights

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseProductApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sum_dependent_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] {M : Type*} [AddCommMonoid M]
    (F : (∀ i, X i) → M) :
    (∑ x, F x) = ∑ a : X 0, ∑ y : ∀ i : Fin n, X i.succ, F (Fin.cons a y) := by
  calc
    _ = ∑ p : X 0 × (∀ i : Fin n, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := Fintype.sum_prod_type _

namespace FiniteProbabilityWeights

theorem complexMean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteProbabilityWeights (X i))
    (F : (∀ i, X i) → ℂ) :
    (pi p).complexMean F = (p 0).complexMean (fun a =>
      (pi (fun i : Fin n => p i.succ)).complexMean (fun y => F (Fin.cons a y))) := by
  change (∑ x, ((∏ i, (p i).weight (x i) : ℝ) : ℂ) * F x) =
    ∑ a, ((p 0).weight a : ℂ) *
      (∑ y, ((∏ i : Fin n, (p i.succ).weight (y i) : ℝ) : ℂ) * F (Fin.cons a y))
  rw [sum_dependent_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_mul_const {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → ℝ) (c : ℝ) : p.mean (fun x => f x * c) = p.mean f * c := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

end FiniteProbabilityWeights

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)]

theorem productMean_coordinateSwap (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (F : (∀ i, X i) → (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => F (productCoordinateMix S x y) (productCoordinateMix S y x))) =
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean (F x)) := by
  let p := FiniteProbabilityWeights.pi μ
  have h : (∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 *
        F (productCoordinateMix S z.1 z.2) (productCoordinateMix S z.2 z.1)) =
      ∑ z : (∀ i, X i) × (∀ i, X i), p.weight z.1 * p.weight z.2 * F z.1 z.2 := by
    apply Fintype.sum_equiv (productCoordinateSwap (X := X) S)
    intro z
    change _ = p.weight (productCoordinateMix S z.1 z.2) *
      p.weight (productCoordinateMix S z.2 z.1) * _
    rw [productCoordinateMix_weight]
    rfl
  simpa only [FiniteProbabilityWeights.mean, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using h

theorem productMean_coordinateMix (μ : ∀ i, FiniteProbabilityWeights (X i))
    (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => (FiniteProbabilityWeights.pi μ).mean
      (fun y => f (productCoordinateMix S x y))) = (FiniteProbabilityWeights.pi μ).mean f := by
  have h := productMean_coordinateSwap μ S (fun x _ => f x)
  simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped Classical

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem density_cauchy_schwarz (r f g : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) :
    (p.mean (fun x => r x * f x * g x)) ^ 2 ≤
      p.mean (fun x => r x * f x ^ 2) * p.mean (fun x => r x * g x ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun x _ => mul_nonneg (p.nonneg x) (mul_nonneg (hr x) (sq_nonneg (f x))))
    (fun x _ => mul_nonneg (p.nonneg x) (mul_nonneg (hr x) (sq_nonneg (g x))))
  intro x _
  exact le_of_eq (by ring)

theorem density_square_le (r f : Ω → ℝ) (hr : ∀ x, 0 ≤ r x) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    p.mean (fun x => r x * f x ^ 2) ≤ M * p.mean (fun x => r x * f x) := by
  rw [← p.mean_const_mul]
  apply p.mean_mono
  intro x
  have h := mul_le_mul_of_nonneg_left (hf x).2 (mul_nonneg (hr x) (hf x).1)
  nlinarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.mul {I : Type*} [DecidableEq I] {X : I → Type*}
    {S T : Finset I} {f g : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (hg : ProductDependsOn T g) :
    ProductDependsOn (S ∪ T) (fun x => f x * g x) := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y (fun i hi => h i (Finset.mem_union_left T hi)),
    hg x y (fun i hi => h i (Finset.mem_union_right S hi))]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp only [productConditionalMean, productCoordinateMix_empty]

theorem productConditionalMean_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => c * f y) x = c * productConditionalMean μ S f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul _ _

theorem productConditionalMean_sum {J : Type*} (s : Finset J) (S : Finset I)
    (f : J → (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ S (fun y => ∑ j ∈ s, f j y) x =
      ∑ j ∈ s, productConditionalMean μ S (f j) x :=
  (FiniteProbabilityWeights.pi μ).mean_sum _ _

theorem productConditionalMean_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productConditionalMean μ S f) := by
  intro x y hxy
  unfold productConditionalMean
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [productCoordinateMix, hi, hxy i hi]
  · simp [productCoordinateMix, hi]

theorem productConditionalMean_of_depends (S : Finset I) {f : (∀ i, X i) → ℝ}
    (hf : ProductDependsOn S f) (x : ∀ i, X i) : productConditionalMean μ S f x = f x := by
  have hpoint (y : ∀ i, X i) : f (productCoordinateMix S x y) = f x := by
    apply hf
    intro i hi
    simp [productCoordinateMix, hi]
  simp only [productConditionalMean, hpoint, FiniteProbabilityWeights.mean_const]

theorem productConditionalMean_comp (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ S (productConditionalMean μ T f) x =
      productConditionalMean μ (S ∩ T) f x := by
  simp only [productConditionalMean, productCoordinateMix_comp]
  exact productMean_coordinateMix μ T (fun y => f (productCoordinateMix (S ∩ T) x y))

theorem productConditionalMean_selfadjoint (S : Finset I) (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productConditionalMean μ S g x) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => productConditionalMean μ S f x * g x) := by
  have h := productMean_coordinateSwap μ S
    (fun x y => f x * g (productCoordinateMix S x y))
  simp only [productCoordinateMix_swap] at h
  unfold productConditionalMean
  simp_rw [← FiniteProbabilityWeights.mean_const_mul, ← FiniteProbabilityWeights.mean_mul_const]
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem finiteWeightDensity_nonneg (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (x : Ω) : 0 ≤ finiteWeightDensity p w x :=
  div_nonneg (hw x) (p.nonneg x)

theorem finiteWeightDensity_mul (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (hsupport : ∀ x, p.weight x = 0 → w x = 0) (x : Ω) :
    p.weight x * finiteWeightDensity p w x = w x := by
  by_cases hx : p.weight x = 0
  · rw [hx, zero_mul, hsupport x hx]
  · unfold finiteWeightDensity
    field_simp

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem productFiberIndicator_depends {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : ProductDependsOn S (productFiberIndicator S x) := by
  intro y z hyz
  have he : (∀ i ∈ S, y i = x i) ↔ (∀ i ∈ S, z i = x i) :=
    ⟨fun h i hi => (hyz i hi).symm.trans (h i hi),
      fun h i hi => (hyz i hi).trans (h i hi)⟩
  simp only [productFiberIndicator, he]

theorem productFiberIndicator_self {I : Type*} {X : I → Type*}
    (S : Finset I) (x : ∀ i, X i) : productFiberIndicator S x x = 1 := by
  simp [productFiberIndicator]

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

theorem weight_le_productFiberMass (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : w x ≤ productFiberMass w S x := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => w y * productFiberIndicator S x y)
    (fun y _ => mul_nonneg (hw y) (by unfold productFiberIndicator; split_ifs <;> norm_num))
    (Finset.mem_univ x)
  simpa only [productFiberMass, productFiberIndicator_self, mul_one] using h

theorem productFiberMass_pos (p : FiniteProbabilityWeights (∀ i, X i))
    (S : Finset I) (x : ∀ i, X i) (hx : 0 < p.weight x) : 0 < productFiberMass p.weight S x :=
  hx.trans_le (weight_le_productFiberMass p.weight p.nonneg S x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productConditionalMean_fiber_identity (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x * productConditionalMean μ S f x =
      productFiberMass (fun y => (FiniteProbabilityWeights.pi μ).weight y * f y) S x := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S f (productFiberIndicator S x)
  simp_rw [productConditionalMean_of_depends μ S (productFiberIndicator_depends S x)] at he
  calc
    _ = p.mean (fun y => productConditionalMean μ S f y * productFiberIndicator S x y) := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      dsimp only
      by_cases hxy : ∀ i ∈ S, y i = x i
      · have hv := productConditionalMean_depends μ S f y x hxy
        rw [hv]
        dsimp [p]
        ring
      · simp only [productFiberIndicator, hxy, ite_false, mul_zero, zero_mul]
    _ = p.mean (fun y => f y * productFiberIndicator S x y) := he.symm
    _ = _ := by
      unfold productFiberMass FiniteProbabilityWeights.mean
      apply Finset.sum_congr rfl
      intro y _
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productFiberMass_fiberMean {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ)
    (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (fun y => p.fiberMean F y f) S x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  classical
  simp only [productFiberMass, FiniteProbabilityWeights.fiberMean, FiniteProbabilityWeights.mean,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp [mul_ite, ite_mul, eq_comm, mul_assoc]

theorem observedProductDensity_fiber_identity {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productFiberMass (FiniteProbabilityWeights.pi μ).weight S x *
        productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) := by
  have hpos : ∀ y, 0 < (FiniteProbabilityWeights.pi μ).weight y :=
    fun y => Finset.prod_pos (fun i _ => hμ i (y i))
  rw [productConditionalMean_fiber_identity]
  have heq : (fun y => (FiniteProbabilityWeights.pi μ).weight y * observedProductDensity μ p F f y) =
      (fun y => p.fiberMean F y f) := by
    funext y
    exact finiteWeightDensity_mul _ _ (fun z hz => False.elim ((hpos z).ne' hz)) y
  rw [heq]
  exact productFiberMass_fiberMean p F f S x

theorem observedProductDensity_conditional {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (hμ : ∀ i x, 0 < (μ i).weight x) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (f : Ω → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productConditionalMean μ S (observedProductDensity μ p F f) x =
      p.mean (fun z => f z * productFiberIndicator S x (F z)) /
        productFiberMass (FiniteProbabilityWeights.pi μ).weight S x := by
  have hp : 0 < (FiniteProbabilityWeights.pi μ).weight x :=
    Finset.prod_pos (fun i _ => hμ i (x i))
  apply (eq_div_iff (productFiberMass_pos _ S x hp).ne').mpr
  simpa only [mul_comm] using observedProductDensity_fiber_identity μ hμ p F f S x

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMeanPullback
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

theorem productMean_reindex (μ : ∀ i, FiniteProbabilityWeights (X i))
    (e : J ≃ I) (g : (∀ j, X (e j)) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => g (fun j => x (e j))) =
      (FiniteProbabilityWeights.pi (fun j => μ (e j))).mean g := by
  classical
  apply Fintype.sum_equiv (Equiv.piCongrLeft X e).symm
  intro x
  change (∏ i, (μ i).weight (x i)) * g (fun j => x (e j)) =
    (∏ j, (μ (e j)).weight (x (e j))) * g (fun j => x (e j))
  rw [e.prod_comp (fun i => (μ i).weight (x i))]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [DecidableEq I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]

omit [Fintype ι] in
theorem productFiberIndicator_partition (I : Finset ι) (base : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    (∑ a : ∀ i : I, X i, productFiberIndicator I (productSubtypePoint I a base) x * f x) = f x := by
  rw [← Finset.sum_mul, productFiberIndicator_sum_subtype, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [DecidableEq I] [Fintype J] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

section

namespace Erdos3

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {X : I → Type*} [∀ i, Fintype (X i)]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RestrictedDegreeSupports
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (I : Type*) [Fintype I] [DecidableEq I]

theorem mem_lowDegreeCoordinateSets (b : ℕ) (S : Finset I) :
    S ∈ lowDegreeCoordinateSets I b ↔ S.card ≤ b := by
  simp only [lowDegreeCoordinateSets, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨j, hj, hcard⟩
    omega
  · intro h
    exact ⟨S.card, by omega, rfl⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem mem_restrictedDegreeSupports (J S : Finset ι) (b : ℕ) :
    S ∈ restrictedDegreeSupports J b ↔ S ⊆ J ∧ S.card ≤ b := by
  simp only [restrictedDegreeSupports, Finset.mem_filter, Finset.mem_powerset]

omit [DecidableEq ι] in
theorem mem_degreeTailSupports (J S : Finset ι) (r b : ℕ) :
    S ∈ degreeTailSupports J r b ↔ S ⊆ J ∧ r < S.card ∧ S.card ≤ b := by
  simp only [degreeTailSupports, Finset.mem_filter, Finset.mem_powerset]

theorem restrictedDegreeSupports_eq_biUnion (J : Finset ι) (b : ℕ) :
    restrictedDegreeSupports J b = (Finset.range (b + 1)).biUnion (fun k => J.powersetCard k) := by
  ext S
  simp only [mem_restrictedDegreeSupports, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hS, hb⟩
    exact ⟨S.card, by omega, hS, rfl⟩
  · rintro ⟨k, hk, hS, he⟩
    exact ⟨hS, by omega⟩

theorem sum_restrictedDegreeSupports (J : Finset ι) (b : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J b, F S) =
      ∑ k ∈ Finset.range (b + 1), ∑ S ∈ J.powersetCard k, F S := by
  rw [restrictedDegreeSupports_eq_biUnion, Finset.sum_biUnion]
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro S hSi hSj
  exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)

theorem sum_restrictedDegreeSupports_zero (J : Finset ι) (r : ℕ) (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J r, F S) =
      F ∅ + ∑ k ∈ Finset.range r, ∑ S ∈ J.powersetCard (k + 1), F S := by
  rw [sum_restrictedDegreeSupports, Finset.sum_range_succ']
  simp only [Finset.powersetCard_zero, Finset.sum_singleton, add_comm]

theorem sum_restrictedDegreeSupports_split (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    (F : Finset ι → ℝ) :
    (∑ S ∈ restrictedDegreeSupports J b, F S) =
      (∑ S ∈ restrictedDegreeSupports J r, F S) + (∑ S ∈ degreeTailSupports J r b, F S) := by
  have he : restrictedDegreeSupports J b = restrictedDegreeSupports J r ∪ degreeTailSupports J r b := by
    ext S
    simp only [Finset.mem_union, mem_restrictedDegreeSupports, mem_degreeTailSupports]
    constructor
    · rintro ⟨hS, hb⟩
      by_cases hr : S.card ≤ r
      · exact Or.inl ⟨hS, hr⟩
      · exact Or.inr ⟨hS, by omega, hb⟩
    · rintro (⟨hS, hr⟩ | ⟨hS, _, hb⟩)
      · exact ⟨hS, hr.trans hrb⟩
      · exact ⟨hS, hb⟩
  rw [he]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro S hlow htail
  have hl := (mem_restrictedDegreeSupports J S r).mp hlow
  have ht := (mem_degreeTailSupports J S r b).mp htail
  omega

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}

end Erdos3

end

section

namespace Erdos3

namespace ProductCylinder

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

variable [Fintype ι] [∀ i, Fintype (X i)]

end ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self (I : Finset ι) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ I I z f x = f (productCoordinateMix I z x) := by
  simp only [productSectionAverage, productCoordinateMix_left, FiniteProbabilityWeights.mean_const]

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_smul (T A : Finset I) (z : ∀ i, X i) (c : ℝ)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z (fun y => c * f y) x = c * productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul c _

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

variable {μ base f}

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_self_mean (I : Finset ι) (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I z f) =
      productConditionalMean μ I f z := by
  simp only [show productSectionAverage μ I I z f =
    (fun x => f (productCoordinateMix I z x)) from funext (productSectionAverage_self μ I z f)]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductMarginalAtomError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productMarginal_test_error (r g : (∀ i, X i) → ℝ) (S : Finset I)
    {η C : ℝ} (hη : 0 ≤ η) (hg : ProductDependsOn S g)
    (hr : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ S r x - 1| ≤ η)
    (hcap : ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |g x| ≤ C) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * g x) -
      (FiniteProbabilityWeights.pi μ).mean g| ≤ η * C := by
  let p := FiniteProbabilityWeights.pi μ
  have he := productConditionalMean_selfadjoint μ S r g
  simp_rw [productConditionalMean_of_depends μ S hg] at he
  have hid : p.mean (fun x => r x * g x) - p.mean g =
      p.mean (fun x => (productConditionalMean μ S r x - 1) * g x) := by
    rw [he, ← p.mean_sub]
    congr 1
    funext x
    ring
  rw [hid]
  apply p.abs_mean_le_on_support
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (hr x hx) (hcap x hx) (abs_nonneg _) hη

theorem productConditionalMean_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (S : Finset I) (x : ∀ i, X i) :
    0 ≤ productConditionalMean μ S (fun y => r y * f y) x ∧
      productConditionalMean μ S (fun y => r y * f y) x ≤ M * productConditionalMean μ S r x := by
  constructor
  · exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun y =>
      mul_nonneg (hr _) (hf _).1)
  · unfold productConditionalMean
    rw [← FiniteProbabilityWeights.mean_const_mul]
    apply FiniteProbabilityWeights.mean_mono
    intro y
    simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hf _).2 (hr _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productFamily_square_comparison (r : (∀ i, X i) → ℝ)
    (D : Finset (Finset I)) (u : Finset I → (∀ i, X i) → ℝ) {b : ℕ} {η C : ℝ}
    (hη : 0 ≤ η) (hC : 0 ≤ C) (hcard : ∀ S ∈ D, S.card ≤ b)
    (hdep : ∀ S ∈ D, ProductDependsOn S (u S))
    (hcap : ∀ S ∈ D, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u S x| ≤ C)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => r x * (∑ S ∈ D, u S x) ^ 2) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ S ∈ D, u S x) ^ 2)| ≤
        η * (D.card : ℝ) ^ 2 * C ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  have hid : p.mean (fun x => r x * (∑ S ∈ D, u S x) ^ 2) -
      p.mean (fun x => (∑ S ∈ D, u S x) ^ 2) =
      ∑ S ∈ D, ∑ T ∈ D,
        (p.mean (fun x => r x * (u S x * u T x)) - p.mean (fun x => u S x * u T x)) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum,
      FiniteProbabilityWeights.mean_sum, Finset.sum_sub_distrib]
    simp only [mul_comm]
  rw [hid]
  calc
    _ ≤ ∑ S ∈ D, ∑ T ∈ D,
        |p.mean (fun x => r x * (u S x * u T x)) - p.mean (fun x => u S x * u T x)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun S _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _S ∈ D, ∑ _T ∈ D, η * C ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      apply productMarginal_test_error μ r (fun x => u S x * u T x) (S ∪ T) hη
        ((hdep S hS).mul (hdep T hT))
      · apply hclose
        exact (Finset.card_union_le S T).trans (by have := hcard S hS; have := hcard T hT; omega)
      · intro x hx
        rw [abs_mul, pow_two]
        exact mul_le_mul (hcap S hS x hx) (hcap T hT x hx) (abs_nonneg _) hC
    _ = _ := by simp; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem alternating_powerset_sum_zero {I : Type*} [DecidableEq I]
    (S : Finset I) {i : I} (hi : i ∈ S) (g : Finset I → ℝ)
    (hpair : ∀ U ⊆ S.erase i, g (insert i U) = g U) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * g U) = 0 := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i S), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro U hU
  have hu := Finset.mem_powerset.mp hU
  have hni : i ∉ U := fun h => Finset.notMem_erase i S (hu h)
  rw [Finset.card_insert_of_notMem hni, pow_succ, hpair U hu]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_depends (S : Finset I) (f : (∀ i, X i) → ℝ) :
    ProductDependsOn S (productANOVA μ S f) := by
  intro x y hxy
  unfold productANOVA
  apply Finset.sum_congr rfl
  intro U _
  congr 1
  exact productConditionalMean_depends μ (S \ U) f x y
    (fun i hi => hxy i (Finset.sdiff_subset hi))

theorem productConditionalMean_ANOVA (S T : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) :
    productConditionalMean μ T (productANOVA μ S f) x =
      if S ⊆ T then productANOVA μ S f x else 0 := by
  classical
  change productConditionalMean μ T (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f y) x =
      if S ⊆ T then (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) else 0
  simp only [productConditionalMean_sum, productConditionalMean_smul, productConditionalMean_comp]
  by_cases hST : S ⊆ T
  · rw [if_pos hST]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hST)]
  · rw [if_neg hST]
    obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hST
    apply alternating_powerset_sum_zero S hi
    intro U _
    have he : T ∩ (S \ insert i U) = T ∩ (S \ U) := by
      ext j
      by_cases hj : j = i
      · subst j
        simp [hni]
      · simp [hj]
    rw [he]

theorem productANOVA_pairing_self (S : Finset I) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x ^ 2) =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVA μ S f x) := by
  let p := FiniteProbabilityWeights.pi μ
  calc
    _ = p.mean (fun x => productANOVA μ S f x * productANOVA μ S f x) := by
      simp only [pow_two]
      rfl
    _ = ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        p.mean (fun x => f x * productConditionalMean μ (S \ U) (productANOVA μ S f) x) := by
      change p.mean (fun x => (∑ U ∈ S.powerset,
        (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x) * productANOVA μ S f x) = _
      simp only [Finset.sum_mul, FiniteProbabilityWeights.mean_sum]
      apply Finset.sum_congr rfl
      intro U _
      calc
        _ = (-1 : ℝ) ^ U.card * p.mean (fun x =>
            productConditionalMean μ (S \ U) f x * productANOVA μ S f x) := by
          rw [← p.mean_const_mul]
          congr 1
          funext x
          ring
        _ = _ := by rw [← productConditionalMean_selfadjoint]
    _ = _ := by
      rw [Finset.sum_eq_single ∅]
      · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
          productConditionalMean_ANOVA, Finset.Subset.refl, ite_true]
        rfl
      · intro U hU hUne
        have hUS := Finset.mem_powerset.mp hU
        have hn : ¬ S ⊆ S \ U := by
          obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hUne
          intro h
          exact (Finset.mem_sdiff.mp (h (hUS hi))).2 hi
        simp only [productConditionalMean_ANOVA, hn, ite_false, mul_zero, p.mean_const]
      · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productANOVA_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : ι → Type*} [∀ i, Fintype (Y i)] (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, Y i) :
    productANOVA ν S (productANOVA ν S f) x = productANOVA ν S f x := by
  rw [productANOVA, Finset.sum_eq_single ∅]
  · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
      productConditionalMean_ANOVA, Finset.Subset.refl, ite_true]
  · intro U hU hne
    have hUS := Finset.mem_powerset.mp hU
    have hn : ¬ S ⊆ S \ U := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      intro h
      exact (Finset.mem_sdiff.mp (h (hUS hi))).2 hi
    simp only [productConditionalMean_ANOVA, hn, ite_false, mul_zero]
  · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_orthogonal_of_not_subset (S T : Finset I) (hTS : ¬ T ⊆ S)
    (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * productANOVA μ T g x) = 0 := by
  have h := productConditionalMean_selfadjoint μ S (productANOVA μ S f) (productANOVA μ T g)
  simpa [productConditionalMean_ANOVA, hTS, FiniteProbabilityWeights.mean_const] using h.symm

theorem productANOVA_orthogonal (S T : Finset I) (hST : S ≠ T)
    (f g : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S f x * productANOVA μ T g x) = 0 := by
  by_cases hTS : T ⊆ S
  · have hn : ¬ S ⊆ T := fun h => hST (Finset.Subset.antisymm h hTS)
    simpa only [mul_comm] using productANOVA_orthogonal_of_not_subset μ T S hn g f
  · exact productANOVA_orthogonal_of_not_subset μ S T hTS f g

theorem productANOVAEnergy_nonneg (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    0 ≤ productANOVAEnergy μ D f :=
  Finset.sum_nonneg (fun _ _ => (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _))

theorem productANOVAEnergy_pairing (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVATruncation μ D f x) := by
  simp only [productANOVAEnergy, productANOVATruncation, Finset.mul_sum,
    FiniteProbabilityWeights.mean_sum, productANOVA_pairing_self]

theorem productANOVAEnergy_square (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVATruncation μ D f x ^ 2) =
      productANOVAEnergy μ D f := by
  simp only [productANOVATruncation, productANOVAEnergy, pow_two, Finset.sum_mul,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    exact productANOVA_orthogonal μ T S hTS f f
  · exact fun h => False.elim (h hS)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_abs_le (S : Finset I) (f : (∀ i, X i) → ℝ)
    (x : ∀ i, X i) {L : ℝ}
    (hraw : ∀ T ⊆ S, |productConditionalMean μ T f x| ≤ L) :
    |productANOVA μ S f x| ≤ (2 : ℝ) ^ S.card * L := by
  unfold productANOVA
  calc
    _ ≤ ∑ U ∈ S.powerset, |(-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ S.powerset, L := by
      apply Finset.sum_le_sum
      intro U _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        hraw (S \ U) Finset.sdiff_subset
    _ = _ := by simp

theorem productANOVA_weighted_cap (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (S : Finset I)
    (hclose : ∀ T ⊆ S, ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productConditionalMean μ T r x - 1| ≤ η)
    (x : ∀ i, X i) (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    |productANOVA μ S (fun y => r y * f y) x| ≤ (2 : ℝ) ^ S.card * (M * (1 + η)) := by
  apply productANOVA_abs_le μ S _ x
  intro T hT
  have hc := productConditionalMean_weighted_cap μ r f hr hf T x
  rw [abs_of_nonneg hc.1]
  have he := (abs_le.mp (hclose T hT x hx)).2
  exact hc.2.trans (mul_le_mul_of_nonneg_left (by linarith) hM)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVAEnergy_mono {D E : Finset (Finset I)} (hDE : D ⊆ E)
    (f : (∀ i, X i) → ℝ) : productANOVAEnergy μ D f ≤ productANOVAEnergy μ E f := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hDE
  intro U _ _
  exact (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _)

theorem productANOVAEnergy_le_level (D : Finset (Finset I)) (d : ℕ)
    (hD : ∀ U ∈ D, U.card = d) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f ≤ productANOVAEnergy μ (Finset.univ.powersetCard d) f := by
  apply productANOVAEnergy_mono μ _ f
  intro U hU
  exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD U hU⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_nonneg (f : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) (x : ∀ i, X i) :
    0 ≤ observedProductDensity μ p F f x := by
  apply finiteWeightDensity_nonneg
  intro y
  exact p.fiberMean_nonneg F y f hf

theorem observedProductDensity_add (f g : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (fun z => f z + g z) x =
      observedProductDensity μ p F f x + observedProductDensity μ p F g x := by
  classical
  have he : p.fiberMean F x (fun z => f z + g z) = p.fiberMean F x f + p.fiberMean F x g := by
    unfold FiniteProbabilityWeights.fiberMean
    rw [← p.mean_add]
    congr 1
    funext z
    split_ifs <;> simp
  change p.fiberMean F x (fun z => f z + g z) / _ = p.fiberMean F x f / _ + p.fiberMean F x g / _
  rw [he, add_div]

theorem observedProductDensity_mean (hμ : ∀ i x, 0 < (μ i).weight x)
    (f : Ω → ℝ) (base : ∀ i, X i) :
    (FiniteProbabilityWeights.pi μ).mean (observedProductDensity μ p F f) = p.mean f := by
  have h := observedProductDensity_conditional μ hμ p F f ∅ base
  rw [productConditionalMean_empty, productFiberMass_empty, (FiniteProbabilityWeights.pi μ).total,
    div_one] at h
  simpa [productFiberIndicator] using h

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_factor (w : Ω → ℝ) (M : ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) (x : ∀ i, X i) :
    observedProductDensity μ p F w x =
      observedProductDensity μ p F (fun _ => 1) x * p.fiberTest F w x := by
  change p.fiberMean F x w / (FiniteProbabilityWeights.pi μ).weight x =
    (p.fiberMean F x (fun _ => 1) / (FiniteProbabilityWeights.pi μ).weight x) * p.fiberTest F w x
  rw [← p.mass_mul_fiberTest F w M hw x]
  ring

theorem observedProductDensity_bounded_factor (w : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) :
    ∃ f : (∀ i, X i) → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      observedProductDensity μ p F w = (fun x => observedProductDensity μ p F (fun _ => 1) x * f x) := by
  exact ⟨p.fiberTest F w, p.fiberTest_bounds F w M hM hw,
    funext (observedProductDensity_factor μ p F w M hw)⟩

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} {X : ι → Type*}

theorem cut_add_erase (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (z : Ω) :
    c.cut F w z + c.erase F w z = w z := by
  unfold cut erase
  split_ifs <;> simp

variable [Fintype Ω] [Fintype ι] [DecidableEq ι] [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem density_cut (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (x : ∀ i, X i) :
    observedProductDensity μ p F (c.cut F w) x =
      if c.Contains x then observedProductDensity μ p F w x else 0 := by
  classical
  by_cases hx : c.Contains x
  · rw [if_pos hx]
    change p.fiberMean F x (c.cut F w) / _ = p.fiberMean F x w / _
    congr 1
    unfold FiniteProbabilityWeights.fiberMean
    congr 1
    funext z
    by_cases hz : F z = x
    · simp [cut, hz, hx]
    · simp [hz]
  · rw [if_neg hx]
    have he : p.fiberMean F x (c.cut F w) = 0 := by
      calc
        _ = p.mean (fun _ => 0) := by
          unfold FiniteProbabilityWeights.fiberMean
          congr 1
          funext z
          by_cases hz : F z = x
          · simp [cut, hz, hx]
          · simp [hz]
        _ = 0 := p.mean_const 0
    change p.fiberMean F x (c.cut F w) / _ = 0
    rw [he, zero_div]

end Erdos3.ProductCylinder

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  (c : ProductCylinder X) (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ)

theorem mass_cut_self : c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
    c.mass μ base (observedProductDensity μ p F w) := by
  unfold mass productConditionalMean
  congr 1
  funext y
  rw [c.density_cut]
  apply if_pos
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

end Erdos3.ProductCylinder

end

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {Ω ι : Type*} {X : ι → Type*}

end Erdos3

end

section

namespace Erdos3

open ProductCylinder

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

end Erdos3

end

section

namespace Erdos3

theorem CylinderRemovalChain.removed_size_mass {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), cf.1.1.card ≤ j ∧
      τ < cf.1.mass μ base (observedProductDensity μ p F cf.2) := by
  induction hchain with
  | nil =>
    intro cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs d hsize hmass hbounded rest ih =>
    intro cf hcf
    change cf ∈ (d, d.cut F w) :: cs.zip (removedCylinderWeights F (d.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      exact ⟨hsize, by rwa [d.mass_cut_self μ base p F w]⟩
    · exact ih cf hcf

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEquivTransport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [Fintype ι] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
theorem productCoordinateMix_map (F : ∀ i, X i → Y i) (S : Finset ι) (x y : ∀ i, X i) :
    (fun i => F i (productCoordinateMix S x y i)) =
      productCoordinateMix S (fun i => F i (x i)) (fun i => F i (y i)) := by
  funext i
  by_cases hi : i ∈ S <;> simp [productCoordinateMix, hi]

theorem productConditionalMean_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean p S (fun y => f (fun i => F i (y i))) x =
      productConditionalMean q S f (fun i => F i (x i)) := by
  simp only [productConditionalMean, productCoordinateMix_map]
  exact productMean_coordinate_transport p q F hF
    (fun y => f (productCoordinateMix S (fun i => F i (x i)) y))

theorem productANOVA_coordinate_transport (p : ∀ i, FiniteProbabilityWeights (X i))
    (q : ∀ i, FiniteProbabilityWeights (Y i)) (F : ∀ i, X i → Y i)
    (hF : ∀ i (f : Y i → ℝ), (p i).mean (fun x => f (F i x)) = (q i).mean f)
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productANOVA p S (fun y => f (fun i => F i (y i))) x =
      productANOVA q S f (fun i => F i (x i)) := by
  simp only [productANOVA, productConditionalMean_coordinate_transport p q F hF]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteCenteredKernel
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem centeredKernelMatrix_apply (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) (f : Y → ℝ) (x : X) :
    (∑ y, centeredKernelMatrix ν K x y * f y) = (K x).mean f - ν.mean f := by
  simp only [centeredKernelMatrix, sub_mul, Finset.sum_sub_distrib, FiniteProbabilityWeights.mean]

theorem FiniteProbabilityWeights.mean_centered_sq (ν : FiniteProbabilityWeights Y) (f : Y → ℝ) :
    ν.mean (fun y => (f y - ν.mean f) ^ 2) = ν.mean (fun y => f y ^ 2) - (ν.mean f) ^ 2 := by
  calc
    _ = ν.mean (fun y => f y ^ 2 - (2 * ν.mean f) * f y + (ν.mean f) ^ 2) := by
      congr 1
      funext y
      ring
    _ = _ := by
      rw [ν.mean_add, ν.mean_sub, ν.mean_const_mul, ν.mean_const]
      ring

theorem centeredKernelMatrix_sq_le (μ : FiniteProbabilityWeights X) (ν : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ f : Y → ℝ, ν.mean f = 0 →
      μ.mean (fun x => (K x).mean f ^ 2) ≤ C * ν.mean (fun y => f y ^ 2)) (f : Y → ℝ) :
    μ.mean (fun x => (∑ y, centeredKernelMatrix ν K x y * f y) ^ 2) ≤
      C * ν.mean (fun y => f y ^ 2) := by
  have hzero : ν.mean (fun y => f y - ν.mean f) = 0 := by
    rw [ν.mean_sub, ν.mean_const, sub_self]
  have hc := hbound (fun y => f y - ν.mean f) hzero
  have he (x : X) : (K x).mean (fun y => f y - ν.mean f) =
      ∑ y, centeredKernelMatrix ν K x y * f y := by
    rw [centeredKernelMatrix_apply, FiniteProbabilityWeights.mean_sub, FiniteProbabilityWeights.mean_const]
  simp_rw [he] at hc
  rw [ν.mean_centered_sq] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) hC)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderJointMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCoupling_left_mean (f : (∀ i, X i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean (fun z => f (fun i => (z i).1)) =
      (FiniteProbabilityWeights.pi μ).mean f :=
  productMean_coordinate_transport _ μ (fun _ => Prod.fst) (fun i => (c i).left_mean) f

theorem productCouplingPairing_sq_le (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c f g ^ 2 ≤
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x ^ 2) *
      (FiniteProbabilityWeights.pi ν).mean (fun y => g y ^ 2) := by
  have h := (FiniteProbabilityWeights.pi (fun i => (c i).law)).mean_mul_sq_le
    (fun z => f (fun i => (z i).1)) (fun z => g (fun i => (z i).2))
  rw [productCoupling_left_mean c (fun x => f x ^ 2),
    productCoupling_right_mean c (fun y => g y ^ 2)] at h
  exact h

theorem productCouplingPairing_ANOVA_ne (S T : Finset ι) (hST : S ≠ T)
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVA μ S f) (productANOVA ν T g) = 0 := by
  have h := productANOVA_orthogonal (fun i => (c i).law) S T hST
    (fun z => f (fun i => (z i).1)) (fun z => g (fun i => (z i).2))
  simpa only [productCouplingPairing, productANOVA_coordinate_transport _ μ (fun _ => Prod.fst) (fun i => (c i).left_mean),
    productANOVA_coordinate_transport _ ν (fun _ => Prod.snd) (fun i => (c i).right_mean)] using h

theorem productCouplingPairing_truncation (D : Finset (Finset ι))
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D f) (productANOVATruncation ν D g) =
      ∑ S ∈ D, productCouplingPairing c (productANOVA μ S f) (productANOVA ν S g) := by
  simp only [productCouplingPairing, productANOVATruncation, Finset.sum_mul,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_eq_single S]
  · intro T _ hTS
    simpa only [productCouplingPairing] using productCouplingPairing_ANOVA_ne c T S hTS f g
  · exact fun hn => False.elim (hn hS)

theorem productCouplingPairing_truncation_sq_le (D : Finset (Finset ι))
    (f : (∀ i, X i) → ℝ) (g : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D f) (productANOVATruncation ν D g) ^ 2 ≤
      productANOVAEnergy μ D f * productANOVAEnergy ν D g := by
  simpa only [productANOVAEnergy_square] using
    productCouplingPairing_sq_le c (productANOVATruncation μ D f) (productANOVATruncation ν D g)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_sum_right {α : Type*} (s : Finset α)
    (f : (∀ i, X i) → ℝ) (g : α → (∀ i, Y i) → ℝ) :
    productCouplingPairing c f (fun y => ∑ a ∈ s, g a y) =
      ∑ a ∈ s, productCouplingPairing c f (g a) := by
  simp only [productCouplingPairing, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]

theorem productCouplingAtomMass_sum_right (I : Finset ι)
    (x : ∀ i, X i) (base : ∀ i, Y i) :
    (∑ a : ∀ i : I, Y i, productCouplingAtomMass c I x (productSubtypePoint I a base)) =
      productFiberMass (FiniteProbabilityWeights.pi μ).weight I x := by
  simp_rw [← productCouplingPairing_indicators]
  rw [← productCouplingPairing_sum_right]
  simp_rw [productFiberIndicator_sum_subtype]
  simpa only [productCouplingPairing, mul_one, productFiberMass, FiniteProbabilityWeights.mean]
    using productCoupling_left_mean c (productFiberIndicator I x)

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

theorem ProductCylinder.referenceMass_mul_mass (c : ProductCylinder X)
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F w) = p.mean (c.cut F w) := by
  classical
  have h := observedProductDensity_fiber_identity μ hμ p F w c.1 (c.assignment base)
  change c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F w) = _ at h
  rw [h]
  congr 1
  funext z
  unfold productFiberIndicator ProductCylinder.cut
  by_cases hc : c.Contains (F z)
  · have hc' := (c.contains_iff base (F z)).mp hc
    rw [if_pos hc', if_pos hc, mul_one]
  · have hc' : ¬ (∀ i ∈ c.1, F z i = c.assignment base i) :=
      fun hi => hc ((c.contains_iff base (F z)).mpr hi)
    rw [if_neg hc', if_neg hc, mul_zero]

theorem ProductCylinder.referenceMass_mul_cut_mass (c : ProductCylinder X)
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F (c.cut F w)) =
      p.mean (c.cut F w) := by
  rw [c.mass_cut_self μ base p F w]
  exact c.referenceMass_mul_mass μ hμ base p F w

theorem CylinderRemovalChain.reference_mass_sum
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => cf.1.referenceMass μ base * cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum =
      p.mean w - p.mean v := by
  induction hchain with
  | nil => simp only [removedCylinderWeights, List.zip_nil_left, List.map_nil, List.sum_nil, sub_self]
  | @cons w v cs c hsize hmass hbounded rest ih =>
    change c.referenceMass μ base * c.mass μ base (observedProductDensity μ p F (c.cut F w)) +
      ((cs.zip (removedCylinderWeights F (c.erase F w) cs)).map
        (fun cf => cf.1.referenceMass μ base * cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum = _
    rw [c.referenceMass_mul_cut_mass μ hμ base p F w, ih]
    have he : p.mean (c.cut F w) + p.mean (c.erase F w) = p.mean w := by
      rw [← p.mean_add]
      congr 1
      funext z
      exact c.cut_add_erase F w z
    linarith

theorem CylinderRemovalChain.reference_mass_sum_le_one
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => cf.1.referenceMass μ base * cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum ≤ 1 := by
  rw [hchain.reference_mass_sum hμ]
  have hupper : p.mean w ≤ 1 := (p.mean_mono hw).trans_eq (p.mean_const 1)
  have hlower := p.mean_nonneg hv
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.joint_mass_sum_le_one
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
        productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
          cf.1.mass μ base (observedProductDensity μ p F cf.2))).sum ≤ 1 := by
  simp_rw [← Finset.sum_mul, productCouplingAtomMass_sum_right]
  exact hchain.reference_mass_sum_le_one hμ hw hv

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductDensityRepresentative
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_empty (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ ∅ f x = (FiniteProbabilityWeights.pi μ).mean f := by
  simp [productANOVA, productConditionalMean_empty]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorePairingSplit
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_empty (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVA μ ∅ w) (productANOVA ν ∅ f) =
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f := by
  simp only [productCouplingPairing, productANOVA_empty, FiniteProbabilityWeights.mean_const]

theorem productCouplingPairing_core_split (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ (restrictedDegreeSupports J b) w)
      (productANOVATruncation ν (restrictedDegreeSupports J b) f) =
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f +
        (∑ k ∈ Finset.range r, productCouplingPairing c
          (productANOVATruncation μ (J.powersetCard (k + 1)) w)
          (productANOVATruncation ν (J.powersetCard (k + 1)) f)) +
        productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
          (productANOVATruncation ν (degreeTailSupports J r b) f) := by
  simp only [productCouplingPairing_truncation]
  rw [sum_restrictedDegreeSupports_split J hrb, sum_restrictedDegreeSupports_zero,
    productCouplingPairing_empty]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteLowLevelSeries
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem low_level_series_bound {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (r : ℕ) :
    (∑ j ∈ Finset.range r, u ^ (j + 1)) ≤ 2 * u := by
  have hs (n : ℕ) : (∑ j ∈ Finset.range n, u ^ j) ≤ 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [geom_sum_succ]
        nlinarith [mul_le_mul_of_nonneg_left ih hu0]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  nlinarith [mul_le_mul_of_nonneg_right (hs r) hu0]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVASectionNormalizedBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_smul (S : Finset I) (c : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => c * f y) x = c * productANOVA μ S f x := by
  simp only [productANOVA, productConditionalMean_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedUnitTruncation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productTruncatedGram_bound (r f : (∀ i, X i) → ℝ)
    (hr : ∀ x, 0 ≤ r x) {M η : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset I)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ∀ S : Finset I, S.card ≤ 2 * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ S r x - 1| ≤ η) :
    productANOVAEnergy μ D (fun x => r x * f x) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean (fun x => r x * f x) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  let p := FiniteProbabilityWeights.pi μ
  let h := fun x => r x * f x
  let P := productANOVATruncation μ D h
  let A := productANOVAEnergy μ D h
  let B := M * p.mean h
  let C := (2 : ℝ) ^ b * M * (1 + η)
  let E := η * (D.card : ℝ) ^ 2 * C ^ 2
  have hM : 0 ≤ M := (p.mean_nonneg (fun x => (hf x).1)).trans
    ((p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const M))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcap : ∀ S ∈ D, ∀ x, p.weight x ≠ 0 → |productANOVA μ S h x| ≤ C := by
    intro S hS x hx
    have hc := productANOVA_weighted_cap μ r f hr hM hf S
      (fun T hT => hclose T (by
        have := Finset.card_le_card hT
        have := hcard S hS
        omega)) x hx
    have hpw : (2 : ℝ) ^ S.card ≤ (2 : ℝ) ^ b := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) (hcard S hS)
    exact hc.trans (by
      dsimp [C]
      nlinarith [mul_le_mul_of_nonneg_right hpw (mul_nonneg hM (by linarith : 0 ≤ 1 + η))])
  have herr := productFamily_square_comparison μ r D (fun S => productANOVA μ S h)
    hη hC hcard (fun S _ => productANOVA_depends μ S h) hcap hclose
  change |p.mean (fun x => r x * P x ^ 2) - p.mean (fun x => P x ^ 2)| ≤ E at herr
  have hsquare : p.mean (fun x => P x ^ 2) = A := productANOVAEnergy_square μ D h
  rw [hsquare] at herr
  have hpair : p.mean (fun x => r x * f x * P x) = A :=
    (productANOVAEnergy_pairing μ D h).symm
  have hA : 0 ≤ A := productANOVAEnergy_nonneg μ D h
  have hB : 0 ≤ B := mul_nonneg hM (p.mean_nonneg (fun x => mul_nonneg (hr x) (hf x).1))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hP : 0 ≤ p.mean (fun x => r x * P x ^ 2) :=
    p.mean_nonneg (fun x => mul_nonneg (hr x) (sq_nonneg _))
  have hquad : A ^ 2 ≤ B * (A + E) := by
    have hc := p.density_cauchy_schwarz r f P hr
    rw [hpair] at hc
    apply hc.trans
    apply mul_le_mul (p.density_square_le r f hr hf) _ hP hB
    have hh := (abs_le.mp herr).2
    linarith
  have hbound : A ≤ 2 * B + 2 * E := by
    by_contra hn
    have hpos : 0 < A := by linarith
    have h₁ := mul_nonneg (show 0 ≤ A - 2 * B by linarith) (show 0 ≤ A + E by linarith)
    have h₂ := mul_nonneg hpos.le (show 0 ≤ A - 2 * E by linarith)
    nlinarith [sq_pos_of_pos hpos]
  have htwo : ((2 : ℝ) ^ b) ^ 2 = (4 : ℝ) ^ b := by
    rw [← pow_mul, Nat.mul_comm b 2, pow_mul]
    norm_num
  have hEeq : E = η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
    dsimp [E, C]
    rw [mul_pow, mul_pow, htwo]
    ring
  calc
    _ ≤ 2 * B + 2 * E := hbound
    _ = _ := by rw [hEeq]; dsimp [B, h, p]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_truncatedGram_bound (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b)) :
    productANOVAEnergy μ D (observedProductDensity μ p F w) ≤
      2 * M * p.mean w + 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  have h := productTruncatedGram_bound μ (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro z; norm_num)) hf hη D hcard hclose
  rw [← he, observedProductDensity_mean μ p F hμ w base] at h
  exact h

theorem observedProductDensity_small_mass_energy (hμ : ∀ i x, 0 < (μ i).weight x)
    (base : ∀ i, X i) (w : Ω → ℝ) {η τ : ℝ}
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hη : 0 ≤ η) (hmass : p.mean w ≤ τ)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ) :
    productANOVAEnergy μ D (observedProductDensity μ p F w) ≤ 3 * τ := by
  have h := observedProductDensity_truncatedGram_bound μ p F hμ base w zero_le_one hw hη D hcard hclose
  norm_num only [one_pow, mul_one] at h
  linarith

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_truncation_sqrt_le (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  calc
    _ = Real.sqrt (productCouplingPairing c (productANOVATruncation μ D w)
        (productANOVATruncation ν D f) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (productANOVAEnergy μ D w * productANOVAEnergy ν D f) :=
      Real.sqrt_le_sqrt (productCouplingPairing_truncation_sq_le c D w f)
    _ = _ := Real.sqrt_mul (productANOVAEnergy_nonneg μ D w) _

theorem productCouplingPairing_truncation_small_energy (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) {τ N : ℝ}
    (hw : productANOVAEnergy μ D w ≤ 3 * τ)
    (hf : Real.sqrt (productANOVAEnergy ν D f) ≤ N) :
    |productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      Real.sqrt (3 * τ) * N := by
  apply (productCouplingPairing_truncation_sqrt_le c D w f).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hw) hf (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem observedProductDensity_small_mass_pairing {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (hμ : ∀ i x, 0 < (μ i).weight x) (base : ∀ i, X i) (w : Ω → ℝ)
    {η τ N : ℝ} (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hη : 0 ≤ η) (hmass : p.mean w ≤ τ)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (f : (∀ i, Y i) → ℝ) (hf : Real.sqrt (productANOVAEnergy ν D f) ≤ N) :
    |productCouplingPairing c (productANOVATruncation μ D (observedProductDensity μ p F w))
      (productANOVATruncation ν D f)| ≤ Real.sqrt (3 * τ) * N :=
  productCouplingPairing_truncation_small_energy c D _ f
    (observedProductDensity_small_mass_energy μ p F hμ base w hw hη hmass D hcard hclose herr) hf

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialProductDifference
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem product_piecewise_split (S : Finset ι) (a b : ι → ℝ) :
    (∏ i, if i ∈ S then a i else b i) = (∏ i ∈ S, a i) * ∏ i ∈ Finset.univ \ S, b i := by
  rw [Finset.prod_ite]
  have h₁ : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
  have h₂ : Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S := by ext i; simp
  rw [h₁, h₂]

theorem partial_product_difference (S : Finset ι) (a b : ι → ℝ) :
    (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i, if i ∈ S \ U then a i else b i)) =
      ∏ i, if i ∈ S then a i - b i else b i := by
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * (∏ i ∈ S \ U, a i) * ∏ i ∈ U, b i) *
        ∏ i ∈ Finset.univ \ S, b i := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U hU
      have hUS := Finset.mem_powerset.mp hU
      have he : Finset.univ \ (S \ U) = (Finset.univ \ S) ∪ U := by
        ext i
        by_cases hi : i ∈ S <;> by_cases hu : i ∈ U <;> simp_all
      have hd : Disjoint (Finset.univ \ S) U := by
        apply Finset.disjoint_left.mpr
        intro i hi hu
        exact (Finset.mem_sdiff.mp hi).2 (hUS hu)
      rw [product_piecewise_split, he, Finset.prod_union hd]
      ring
    _ = (∏ i ∈ S, (a i - b i)) * ∏ i ∈ Finset.univ \ S, b i := by
      rw [← Finset.prod_sub]
    _ = _ := (product_piecewise_split S (fun i => a i - b i) b).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RetainedShellComparison
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem retained_pairing_upper_with_shell {PH PG m h g v τ lam ε δ EH EG : ℝ}
    (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : PH ≤ m * h + δ * m * lam * (v + τ) + EH)
    (hPG : m * g - δ * m * (v + τ) - EG ≤ PG)
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g) (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ m * lam * (1 + 2 * ε) * τ + EH + (1 + ε) * lam * EG := by
  have hp := mul_le_mul_of_nonneg_left hPG (mul_nonneg (by linarith : 0 ≤ 1 + ε) hlam)
  have hmh := mul_le_mul_of_nonneg_left hh hm
  have hc : PH - (1 + ε) * lam * PG ≤
      m * lam * (τ - ε * g + δ * (2 + ε) * (v + τ)) + EH + (1 + ε) * lam * EG := by
    nlinarith
  have hi : τ - ε * g + δ * (2 + ε) * (v + τ) ≤ (1 + 2 * ε) * τ := by
    nlinarith [mul_le_mul_of_nonneg_left hg hε,
      mul_le_mul_of_nonneg_right hsmall (add_nonneg hv hτ)]
  have hmul := mul_le_mul_of_nonneg_left hi (mul_nonneg hm hlam)
  nlinarith

theorem retained_pairing_abs_with_shell {PH PG m h g v τ lam ε δ EH EG : ℝ}
    (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : |PH - m * h| ≤ EH + δ * m * lam * (v + τ))
    (hPG : |PG - m * g| ≤ EG + δ * m * (v + τ))
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g) (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ m * lam * (1 + 2 * ε) * τ + EH + (1 + ε) * lam * EG := by
  apply retained_pairing_upper_with_shell hm hlam hv hτ hε _ _ hh hg hsmall
  · linarith [(abs_le.mp hPH).2]
  · linarith [(abs_le.mp hPG).1]

theorem retained_atom_from_normalized_errors {PH PG a m h g v τ lam ε δ EH EG UH UG : ℝ}
    (ha : 0 ≤ a) (hm : 0 ≤ m) (hlam : 0 ≤ lam) (hv : 0 ≤ v) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hPH : |PH - (a * m) * h| ≤ EH + a * m * (4 * lam * (v + τ)) * UH)
    (hPG : |PG - (a * m) * g| ≤ EG + a * m * (2 * (v + τ)) * UG)
    (hUH : 4 * UH ≤ δ) (hUG : 2 * UG ≤ δ)
    (hh : h ≤ lam * g + lam * τ) (hg : v - τ ≤ g) (hsmall : δ * (2 + ε) ≤ ε) :
    PH - (1 + ε) * lam * PG ≤ (a * m) * lam * (1 + 2 * ε) * τ + EH + (1 + ε) * lam * EG := by
  apply retained_pairing_abs_with_shell (mul_nonneg ha hm) hlam hv hτ hε _ _ hh hg hsmall
  · have hmul := mul_le_mul_of_nonneg_left hUH
      (mul_nonneg (mul_nonneg (mul_nonneg ha hm) hlam) (add_nonneg hv hτ))
    exact hPH.trans (by nlinarith)
  · have hmul := mul_le_mul_of_nonneg_left hUG
      (mul_nonneg (mul_nonneg ha hm) (add_nonneg hv hτ))
    exact hPG.trans (by nlinarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductKernelPairing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_pi_fin_cons {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (f : (∀ i, X i) → ℝ) :
    (pi p).mean f = (p 0).mean (fun a =>
      (pi (fun i : Fin n => p i.succ)).mean (fun y => f (Fin.cons a y))) := by
  have h := congrArg Complex.re (complexMean_pi_fin_cons p (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

theorem mean_empty_tuple {X : Fin 0 → Type*} [∀ i, Fintype (X i)]
    (p : FiniteProbabilityWeights (∀ i, X i)) (f : (∀ i, X i) → ℝ) :
    p.mean f = f (fun i => Fin.elim0 i) := by
  have hf : f = fun _ => f (fun i => Fin.elim0 i) := by
    funext x
    exact congrArg f (Subsingleton.elim _ _)
  rw [hf, p.mean_const]

end FiniteProbabilityWeights

theorem productMatrixApply_empty {X Y : Fin 0 → Type*} [∀ i, Fintype (Y i)]
    (A : ∀ i, X i → Y i → ℝ) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply A f x = f (fun i => Fin.elim0 i) := by
  classical
  simp only [productMatrixApply, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
  congr 1

theorem productMatrixApply_fin_cons {n : ℕ} {X Y : Fin (n + 1) → Type*}
    [∀ i, Fintype (Y i)] (A : ∀ i, X i → Y i → ℝ) (f : (∀ i, Y i) → ℝ)
    (x : X 0) (u : ∀ i : Fin n, X i.succ) :
    productMatrixApply A f (Fin.cons x u) = ∑ y : Y 0, A 0 x y *
      productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) u := by
  simp only [productMatrixApply, sum_dependent_fin_cons, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum, mul_assoc]

theorem productMatrixApply_sq_le_fin {n : ℕ} {X Y : Fin n → Type*}
    [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (A : ∀ i, X i → Y i → ℝ) (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2)) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply A f x ^ 2) ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  induction n with
  | zero =>
      simp only [productMatrixApply_empty, Fin.prod_univ_zero, one_mul,
        FiniteProbabilityWeights.mean_const, FiniteProbabilityWeights.mean_empty_tuple]
      exact le_rfl
  | succ n ih =>
      rw [FiniteProbabilityWeights.mean_pi_fin_cons]
      simp_rw [productMatrixApply_fin_cons]
      rw [FiniteProbabilityWeights.mean_comm]
      calc
        _ ≤ (FiniteProbabilityWeights.pi (fun i : Fin n => μ i.succ)).mean
            (fun x => C 0 * (ν 0).mean (fun y =>
              productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) x ^ 2)) :=
          FiniteProbabilityWeights.mean_mono _ (fun x => hA 0 _)
        _ = C 0 * (ν 0).mean (fun y =>
            (FiniteProbabilityWeights.pi (fun i : Fin n => μ i.succ)).mean
              (fun x => productMatrixApply (fun i : Fin n => A i.succ) (fun v => f (Fin.cons y v)) x ^ 2)) := by
          rw [FiniteProbabilityWeights.mean_const_mul, FiniteProbabilityWeights.mean_comm]
        _ ≤ C 0 * (ν 0).mean (fun y => (∏ i : Fin n, C i.succ) *
            (FiniteProbabilityWeights.pi (fun i : Fin n => ν i.succ)).mean
              (fun v => f (Fin.cons y v) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (hC 0)
          apply FiniteProbabilityWeights.mean_mono
          intro y
          exact ih (fun i => μ i.succ) (fun i => ν i.succ) (fun i => A i.succ)
            (fun i => C i.succ) (fun i => hC i.succ) (fun i => hA i.succ) (fun v => f (Fin.cons y v))
        _ = _ := by
          rw [FiniteProbabilityWeights.mean_const_mul, Fin.prod_univ_succ,
            FiniteProbabilityWeights.mean_pi_fin_cons]
          ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (X i)] in
theorem productMatrixApply_reindex (A : ∀ i, X i → Y i → ℝ) (e : κ ≃ ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply A f x = productMatrixApply (fun j => A (e j))
      (fun y => f (Equiv.piCongrLeft Y e y)) (fun j => x (e j)) := by
  classical
  unfold productMatrixApply
  apply Fintype.sum_equiv (Equiv.piCongrLeft Y e).symm
  intro y
  simp only [Equiv.apply_symm_apply, Equiv.piCongrLeft_symm_apply]
  rw [e.prod_comp (fun i => A i (x i) (y i))]

omit [Fintype κ] [DecidableEq κ] in
theorem productMatrixApply_sq_le (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (A : ∀ i, X i → Y i → ℝ)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (∑ y, A i x y * f y) ^ 2) ≤
      C i * (ν i).mean (fun y => f y ^ 2)) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply A f x ^ 2) ≤
      (∏ i, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  let e := (Fintype.equivFin ι).symm
  let eY := Equiv.piCongrLeft Y e
  have hh := productMatrixApply_sq_le_fin (fun j => μ (e j)) (fun j => ν (e j))
    (fun j => A (e j)) (fun j => C (e j)) (fun j => hC (e j)) (fun j => hA (e j))
    (fun y => f (eY y))
  have hleft := productMean_reindex μ e
    (fun x => productMatrixApply (fun j => A (e j)) (fun y => f (eY y)) x ^ 2)
  rw [← hleft] at hh
  have heval (x : ∀ i, X i) : productMatrixApply (fun j => A (e j))
      (fun y => f (eY y)) (fun j => x (e j)) = productMatrixApply A f x :=
    (productMatrixApply_reindex A e f x).symm
  simp_rw [heval] at hh
  have hright := productMean_reindex ν e (fun y => f (eY y) ^ 2)
  have he (y : ∀ i, Y i) : eY (fun j => y (e j)) = y := eY.apply_symm_apply y
  simp_rw [he] at hright
  rw [← hright, e.prod_comp C] at hh
  exact hh

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productJoint_mean (μ : ∀ i, FiniteProbabilityWeights (X i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (F : (∀ i, X i) → (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi (fun i => (μ i).joint (K i))).mean
      (fun z => F (fun i => (z i).1) (fun i => (z i).2)) =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => (FiniteProbabilityWeights.pi (fun i => K i (x i))).mean (F x)) := by
  calc
    _ = ∑ z : (∀ i, X i) × (∀ i, Y i),
        (∏ i, (μ i).weight (z.1 i)) * (∏ i, (K i (z.1 i)).weight (z.2 i)) * F z.1 z.2 := by
      apply Fintype.sum_equiv (productPairCoordinates X Y)
      intro z
      change (∏ i, (μ i).weight (z i).1 * (K i (z i).1).weight (z i).2) * _ = _
      rw [Finset.prod_mul_distrib]
      rfl
    _ = _ := by
      simp only [Fintype.sum_prod_type, FiniteProbabilityWeights.mean,
        FiniteProbabilityWeights.pi, Finset.mul_sum, mul_assoc]

theorem productCouplingPairing_ofKernel (μ : ∀ i, FiniteProbabilityWeights (X i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)) w f =
      (FiniteProbabilityWeights.pi μ).mean
        (fun x => w x * productMatrixApply (fun i x y => (K i x).weight y) f x) := by
  change (FiniteProbabilityWeights.pi (fun i => (μ i).joint (K i))).mean
    (fun z => w (fun i => (z i).1) * f (fun i => (z i).2)) = _
  rw [productJoint_mean μ K (fun x y => w x * f y)]
  simp only [FiniteProbabilityWeights.mean_const_mul]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProductMixedLaws
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productMean_mix_laws (p q : ∀ i, FiniteProbabilityWeights (Y i))
    (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi p).mean (fun x => (FiniteProbabilityWeights.pi q).mean
      (fun y => f (productCoordinateMix S x y))) =
      (FiniteProbabilityWeights.pi (fun i => if i ∈ S then p i else q i)).mean f := by
  rw [← productJoint_mean p (fun i _ => q i) (fun x y => f (productCoordinateMix S x y))]
  have h : ∀ i (g : Y i → ℝ), ((p i).joint (fun _ => q i)).mean
      (fun z => g (if i ∈ S then z.1 else z.2)) =
        (if i ∈ S then p i else q i).mean g := by
    intro i g
    by_cases hi : i ∈ S
    · simp only [hi, ite_true, FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
    · simp only [hi, ite_false, FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
  unfold productCoordinateMix
  exact productMean_coordinate_transport (fun i => (p i).joint (fun _ => q i))
      (fun i => if i ∈ S then p i else q i)
      (fun i (z : Y i × Y i) => if i ∈ S then z.1 else z.2) h f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelSupportContraction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productKernelApply_conditional (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (ν : ∀ i, FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (productConditionalMean ν S f) x =
      (FiniteProbabilityWeights.pi (fun i => if i ∈ S then K i (x i) else ν i)).mean f :=
  productMean_mix_laws (fun i => K i (x i)) ν S f

theorem productKernelApply_sum {J : Type*} (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (D : Finset J) (f : J → (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (fun y => ∑ j ∈ D, f j y) x = ∑ j ∈ D, productKernelApply K (f j) x :=
  FiniteProbabilityWeights.mean_sum _ D f

theorem productKernelApply_smul (K : ∀ i, X i → FiniteProbabilityWeights (Y i))
    (c : ℝ) (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (fun y => c * f y) x = c * productKernelApply K f x :=
  FiniteProbabilityWeights.mean_const_mul _ c f

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (Y i)]

theorem productKernelApply_ANOVA (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productKernelApply K (productANOVA ν S f) x = productMatrixApply (anovaKernelMatrix ν K S) f x := by
  have hT (T : Finset ι) : productKernelApply K (productConditionalMean ν T f) x =
      ∑ y, (∏ i, if i ∈ T then (K i (x i)).weight (y i) else (ν i).weight (y i)) * f y := by
    rw [productKernelApply_conditional]
    simp only [FiniteProbabilityWeights.mean, FiniteProbabilityWeights.pi]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ T <;> simp only [hi, ite_true, ite_false]
  change productKernelApply K (fun y => ∑ U ∈ S.powerset,
    (-1 : ℝ) ^ U.card * productConditionalMean ν (S \ U) f y) x = _
  rw [productKernelApply_sum]
  simp_rw [productKernelApply_smul, hT, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold productMatrixApply
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card *
        (∏ i, if i ∈ S \ U then (K i (x i)).weight (y i) else (ν i).weight (y i))) * f y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ = _ := by
      rw [partial_product_difference]
      rfl

theorem productKernelApply_ANOVA_active (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (S : Finset ι)
    (f : (∀ i, Y i) → ℝ) (x : ∀ i, X i) :
    productMatrixApply (anovaKernelMatrix ν K S) (productANOVA ν S f) x =
      productKernelApply K (productANOVA ν S f) x := by
  rw [← productKernelApply_ANOVA]
  have he : productANOVA ν S (productANOVA ν S f) = productANOVA ν S f :=
    funext (productANOVA_idempotent ν S f)
  rw [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))

include hC hbound

theorem anovaKernelMatrix_sq_le (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productMatrixApply (anovaKernelMatrix ν K S) f x ^ 2) ≤
      (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => f y ^ 2) := by
  have hc (i : ι) : 0 ≤ if i ∈ S then C i else 1 := by
    split_ifs
    · exact hC i
    · exact zero_le_one
  have ha (i : ι) (g : Y i → ℝ) :
      (μ i).mean (fun x => (∑ y, anovaKernelMatrix ν K S i x y * g y) ^ 2) ≤
        (if i ∈ S then C i else 1) * (ν i).mean (fun y => g y ^ 2) := by
    by_cases hi : i ∈ S
    · simp only [anovaKernelMatrix, hi, ite_true]
      exact centeredKernelMatrix_sq_le (μ i) (ν i) (K i) (hC i) (hbound i) g
    · simp only [anovaKernelMatrix, hi, ite_false, one_mul]
      change (μ i).mean (fun _ => (ν i).mean g ^ 2) ≤ _
      rw [FiniteProbabilityWeights.mean_const]
      exact (ν i).mean_square_le g
  simpa only [Fintype.prod_ite_mem] using
    productMatrixApply_sq_le μ ν (anovaKernelMatrix ν K S) (fun i => if i ∈ S then C i else 1) hc ha f

theorem productKernelApply_ANOVA_sq_le (S : Finset ι) (f : (∀ i, Y i) → ℝ) :
    (FiniteProbabilityWeights.pi μ).mean (fun x => productKernelApply K (productANOVA ν S f) x ^ 2) ≤
      (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi ν).mean (fun y => productANOVA ν S f y ^ 2) := by
  simpa only [productKernelApply_ANOVA_active] using
    anovaKernelMatrix_sq_le μ ν K C hC hbound S (productANOVA ν S f)

theorem productCouplingPairing_support_sq_le
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (S : Finset ι) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVA μ S w) (productANOVA ν S f) ^ 2 ≤
        (∏ i ∈ S, C i) * (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2) *
          (FiniteProbabilityWeights.pi ν).mean (fun y => productANOVA ν S f y ^ 2) := by
  rw [productCouplingPairing_ofKernel]
  change ((FiniteProbabilityWeights.pi μ).mean
    (fun x => productANOVA μ S w x * productKernelApply K (productANOVA ν S f) x)) ^ 2 ≤ _
  have hcs := (FiniteProbabilityWeights.pi μ).mean_mul_sq_le (productANOVA μ S w)
    (productKernelApply K (productANOVA ν S f))
  have hn := productKernelApply_ANOVA_sq_le μ ν K C hC hbound S f
  have hm := mul_le_mul_of_nonneg_left hn
    ((FiniteProbabilityWeights.pi μ).mean_nonneg (fun x => sq_nonneg (productANOVA μ S w x)))
  exact (hcs.trans hm).trans_eq (by ring)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportPairingAggregation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productCouplingPairing_truncation_abs_le
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (D : Finset (Finset ι)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hprod : ∀ S ∈ D, (∏ i ∈ S, C i) ≤ ρ ^ 2)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
        ρ * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have ha (S : Finset ι) : 0 ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2) :=
    FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (productANOVA μ S w x))
  have hb (S : Finset ι) : 0 ≤ (FiniteProbabilityWeights.pi ν).mean (fun x => productANOVA ν S f x ^ 2) :=
    FiniteProbabilityWeights.mean_nonneg _ (fun x => sq_nonneg (productANOVA ν S f x))
  have hpoint (S : Finset ι) (hS : S ∈ D) :
      productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f) ^ 2 ≤
        (ρ ^ 2 * (FiniteProbabilityWeights.pi μ).mean (fun x => productANOVA μ S w x ^ 2)) *
          (FiniteProbabilityWeights.pi ν).mean (fun x => productANOVA ν S f x ^ 2) :=
    (productCouplingPairing_support_sq_le μ ν K C hC hbound hK S w f).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hprod S hS) (ha S)) (hb S))
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul D
    (fun S _ => mul_nonneg (sq_nonneg ρ) (ha S)) (fun S _ => hb S) hpoint
  rw [← Finset.mul_sum] at hs
  change (∑ S ∈ D, productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f)) ^ 2 ≤
    ρ ^ 2 * productANOVAEnergy μ D w * productANOVAEnergy ν D f at hs
  rw [productCouplingPairing_truncation]
  calc
    _ = Real.sqrt ((∑ S ∈ D, productCouplingPairing c (productANOVA μ S w) (productANOVA ν S f)) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (ρ ^ 2 * productANOVAEnergy μ D w * productANOVAEnergy ν D f) := Real.sqrt_le_sqrt hs
    _ = _ := by
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg ρ) (productANOVAEnergy_nonneg μ D w)),
        Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoreComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
  (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)

include hC hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productCouplingPairing_restricted_tail_abs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (J : Finset ι) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∈ J, C i ≤ κ ^ 2) (r : ℕ) (D : Finset (Finset ι))
    (hsub : ∀ S ∈ D, S ⊆ J) (hmin : ∀ S ∈ D, r ≤ S.card)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ D w) (productANOVATruncation ν D f)| ≤
      κ ^ r * Real.sqrt (productANOVAEnergy μ D w) * Real.sqrt (productANOVAEnergy ν D f) := by
  apply productCouplingPairing_truncation_abs_le μ ν K C hC hbound hK D (pow_nonneg hκ0 r) _ w f
  intro S hS
  have hp : (∏ i ∈ S, C i) ≤ (κ ^ S.card) ^ 2 := by
    calc
      _ ≤ ∏ _i ∈ S, κ ^ 2 := Finset.prod_le_prod (fun i _ => hC i) (fun i hi => hcap i (hsub S hS hi))
      _ = _ := by rw [Finset.prod_const, ← pow_mul, ← pow_mul, Nat.mul_comm 2 S.card]
  exact hp.trans (pow_le_pow_left₀ (pow_nonneg hκ0 S.card)
    (pow_le_pow_of_le_one hκ0 hκ1 (hmin S hS)) 2)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
  (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)

include hC hbound

theorem productCouplingPairing_restricted_level_of_bounds (J : Finset ι)
    {κ A B : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (k : ℕ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A)
    (hf : Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B) :
    |productCouplingPairing (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (J.powersetCard k) w)
      (productANOVATruncation ν (J.powersetCard k) f)| ≤ κ ^ k * A * B := by
  have hcard (S : Finset ι) (hS : S ∈ J.powersetCard k) := (Finset.mem_powersetCard.mp hS).2
  have hwr := (Real.sqrt_le_sqrt (productANOVAEnergy_le_level μ (J.powersetCard k) k hcard w)).trans hw
  have hfr := (Real.sqrt_le_sqrt (productANOVAEnergy_le_level ν (J.powersetCard k) k hcard f)).trans hf
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK J hκ0 hκ1 hcap k
    (J.powersetCard k) (fun S hS => (Finset.mem_powersetCard.mp hS).1)
    (fun S hS => (hcard S hS).ge) w f
  apply ht.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left hwr (pow_nonneg hκ0 k)) hfr (Real.sqrt_nonneg _)
    (mul_nonneg (pow_nonneg hκ0 k) ((Real.sqrt_nonneg _).trans hwr))

theorem productCouplingPairing_restricted_low_levels_small (J : Finset ι)
    {κ A B : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2) (r : ℕ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k)) :
    |∑ j ∈ Finset.range r, productCouplingPairing
      (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
      (productANOVATruncation μ (J.powersetCard (j + 1)) w)
      (productANOVATruncation ν (J.powersetCard (j + 1)) f)| ≤ 2 * (κ * A ^ 2 * B ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range r, |productCouplingPairing
        (fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i))
        (productANOVATruncation μ (J.powersetCard (j + 1)) w)
        (productANOVATruncation ν (J.powersetCard (j + 1)) f)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range r, (κ * A ^ 2 * B ^ 2) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hle : j + 1 ≤ r := Finset.mem_range.mp hj
      have hb := productCouplingPairing_restricted_level_of_bounds μ ν K C hC hbound hK J hκ0 hκ1 hcap
        (j + 1) w f (hw (j + 1) (by omega) hle) (hf (j + 1) (by omega) hle)
      exact hb.trans_eq (by rw [mul_pow, mul_pow, pow_mul, pow_mul])
    _ ≤ _ := low_level_series_bound (by positivity) hsmall r

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_core_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (J : Finset ι) {r b : ℕ} (hrb : r ≤ b)
    {κ A B M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∈ J, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) w) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k) f) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) w) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) f) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c (productANOVATruncation μ (restrictedDegreeSupports J b) w)
      (productANOVATruncation ν (restrictedDegreeSupports J b) f) -
      (FiniteProbabilityWeights.pi μ).mean w * (FiniteProbabilityWeights.pi ν).mean f| ≤
      2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hlo := productCouplingPairing_restricted_low_levels_small μ ν K C hC hbound hK J
    hκ0 hκ1 hcap hsmall r w f hw hf
  have hsub : degreeTailSupports J r b ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    exact (mem_lowDegreeCoordinateSets ι b S).mpr ((mem_degreeTailSupports J S r b).mp hS).2.2
  have hwm := (Real.sqrt_le_sqrt (productANOVAEnergy_mono μ hsub w)).trans hM
  have hfn := (Real.sqrt_le_sqrt (productANOVAEnergy_mono ν hsub f)).trans hN
  have ht := productCouplingPairing_restricted_tail_abs_le μ ν K C hC hbound hK J hκ0 hκ1 hcap r
    (degreeTailSupports J r b) (fun S hS => ((mem_degreeTailSupports J S r b).mp hS).1)
    (fun S hS => ((mem_degreeTailSupports J S r b).mp hS).2.1.le) w f
  have htail : |productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
      (productANOVATruncation ν (degreeTailSupports J r b) f)| ≤ κ ^ r * M * N :=
    ht.trans (mul_le_mul (mul_le_mul_of_nonneg_left hwm (pow_nonneg hκ0 r)) hfn
      (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hκ0 r) ((Real.sqrt_nonneg _).trans hwm)))
  calc
    _ = |(∑ k ∈ Finset.range r, productCouplingPairing c
          (productANOVATruncation μ (J.powersetCard (k + 1)) w)
          (productANOVATruncation ν (J.powersetCard (k + 1)) f)) +
        productCouplingPairing c (productANOVATruncation μ (degreeTailSupports J r b) w)
          (productANOVATruncation ν (degreeTailSupports J r b) f)| := by
      rw [productCouplingPairing_core_split c J hrb]
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hlo htail)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledConditionedComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productANOVA_sum (μ : ∀ i, FiniteProbabilityWeights (X i))
    {α : Type*} (s : Finset α) (f : α → (∀ i, X i) → ℝ) (S : Finset ι) (x : ∀ i, X i) :
    productANOVA μ S (fun y => ∑ a ∈ s, f a y) x = ∑ a ∈ s, productANOVA μ S (f a) x := by
  simp only [productANOVA, productConditionalMean, FiniteProbabilityWeights.mean_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem productANOVATruncation_sum (μ : ∀ i, FiniteProbabilityWeights (X i))
    {α : Type*} (s : Finset α) (f : α → (∀ i, X i) → ℝ) (D : Finset (Finset ι)) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => ∑ a ∈ s, f a y) x =
      ∑ a ∈ s, productANOVATruncation μ D (f a) x := by
  simp only [productANOVATruncation, productANOVA_sum]
  rw [Finset.sum_comm]

theorem productANOVATruncation_smul (μ : ∀ i, FiniteProbabilityWeights (X i))
    (D : Finset (Finset ι)) (a : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => a * f y) x = a * productANOVATruncation μ D f x := by
  simp only [productANOVATruncation, productANOVA_smul, Finset.mul_sum]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_smul (a b : ℝ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (fun x => a * w x) (fun y => b * f y) = a * b * productCouplingPairing c w f := by
  unfold productCouplingPairing
  rw [← FiniteProbabilityWeights.mean_const_mul]
  congr 1
  funext z
  ring

theorem productCouplingPairing_truncation_smul (D : Finset (Finset ι)) (a b : ℝ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productCouplingPairing c (productANOVATruncation μ D (fun x => a * w x))
      (productANOVATruncation ν D (fun y => b * f y)) =
      a * b * productCouplingPairing c (productANOVATruncation μ D w) (productANOVATruncation ν D f) := by
  simp only [show productANOVATruncation μ D (fun x => a * w x) =
      (fun x => a * productANOVATruncation μ D w x) from funext (productANOVATruncation_smul μ D a w),
    show productANOVATruncation ν D (fun y => b * f y) =
      (fun y => b * productANOVATruncation ν D f y) from funext (productANOVATruncation_smul ν D b f),
    productCouplingPairing_smul]

end Erdos3

end

section

namespace Erdos3

theorem normalized_pairing_error_scale {P u v q m s E : ℝ} (hm : 0 < m) (hs : 0 < s)
    (h : |m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v))| ≤ E) :
    |P - q * (u * v)| ≤ m * s * E := by
  calc
    _ = |(m * s) * (m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v)))| := by
      congr 1
      field_simp
    _ = m * s * |m⁻¹ * s⁻¹ * P - q * ((m⁻¹ * u) * (s⁻¹ * v))| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hm.le hs.le)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (mul_nonneg hm.le hs.le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productAtomTruncatedPairing_smul (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (a b : ℝ) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productAtomTruncatedPairing c D I x y (fun z => a * w z) (fun z => b * f z) =
      a * b * productAtomTruncatedPairing c D I x y w f := by
  have hw : (fun z => productFiberIndicator I x z * (a * w z)) =
      (fun z => a * (productFiberIndicator I x z * w z)) := by funext z; ring
  have hf : (fun z => productFiberIndicator I y z * (b * f z)) =
      (fun z => b * (productFiberIndicator I y z * f z)) := by funext z; ring
  unfold productAtomTruncatedPairing
  rw [hw, hf, productCouplingPairing_truncation_smul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

theorem productANOVA_add (μ : ∀ i, FiniteProbabilityWeights (X i)) (S : Finset ι)
    (f g : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVA μ S (fun y => f y + g y) x = productANOVA μ S f x + productANOVA μ S g x := by
  simp only [productANOVA, productConditionalMean, FiniteProbabilityWeights.mean_add,
    mul_add, Finset.sum_add_distrib]

theorem productANOVATruncation_add (μ : ∀ i, FiniteProbabilityWeights (X i)) (D : Finset (Finset ι))
    (f g : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productANOVATruncation μ D (fun y => f y + g y) x =
      productANOVATruncation μ D f x + productANOVATruncation μ D g x := by
  simp only [productANOVATruncation, productANOVA_add, Finset.sum_add_distrib]

variable {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_add_left (D : Finset (Finset ι))
    (u w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => u x + w x) f =
      productTruncatedPairing c D u f + productTruncatedPairing c D w f := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_add,
    add_mul, FiniteProbabilityWeights.mean_add]

theorem productTruncatedPairing_add_right (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun x => f x + g x) =
      productTruncatedPairing c D w f + productTruncatedPairing c D w g := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_add,
    mul_add, FiniteProbabilityWeights.mean_add]

theorem productTruncatedPairing_smul (D : Finset (Finset ι)) (a b : ℝ)
    (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (fun x => a * w x) (fun y => b * f y) =
      a * b * productTruncatedPairing c D w f := productCouplingPairing_truncation_smul c D a b w f

theorem productTruncatedPairing_sub_smul_right (D : Finset (Finset ι)) (a : ℝ)
    (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => f y - a * g y) =
      productTruncatedPairing c D w f - a * productTruncatedPairing c D w g := by
  have he : (fun y => f y - a * g y) = (fun y => f y + (-a) * g y) := by funext y; ring
  have hs := productTruncatedPairing_smul c D 1 (-a) w g
  simp only [one_mul] at hs
  rw [he, productTruncatedPairing_add_right, hs]
  ring

theorem productTruncatedPairing_sum_right {α : Type*} (s : Finset α) (D : Finset (Finset ι))
    (w : (∀ i, X i) → ℝ) (f : α → (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D w (fun y => ∑ a ∈ s, f a y) =
      ∑ a ∈ s, productTruncatedPairing c D w (f a) := by
  simp only [productTruncatedPairing, productCouplingPairing, productANOVATruncation_sum,
    Finset.mul_sum, FiniteProbabilityWeights.mean_sum]

theorem productAtomTruncatedPairing_sub_smul_right (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (y : ∀ i, Y i) (a : ℝ) (w : (∀ i, X i) → ℝ) (f g : (∀ i, Y i) → ℝ) :
    productAtomTruncatedPairing c D I x y w (fun z => f z - a * g z) =
      productAtomTruncatedPairing c D I x y w f - a * productAtomTruncatedPairing c D I x y w g := by
  have he : (fun z => productFiberIndicator I y z * (f z - a * g z)) =
      (fun z => productFiberIndicator I y z * f z - a * (productFiberIndicator I y z * g z)) := by
    funext z
    ring
  change productTruncatedPairing c D (fun z => productFiberIndicator I x z * w z) _ = _
  rw [he, productTruncatedPairing_sub_smul_right]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productTruncatedPairing_atom_sum_right (D : Finset (Finset ι)) (I : Finset ι)
    (x : ∀ i, X i) (baseY : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ) :
    (∑ a : ∀ i : I, Y i, productAtomTruncatedPairing c D I x (productSubtypePoint I a baseY) w f) =
      productTruncatedPairing c D (fun z => productFiberIndicator I x z * w z) f := by
  change (∑ a : ∀ i : I, Y i, productTruncatedPairing c D
    (fun z => productFiberIndicator I x z * w z)
    (fun z => productFiberIndicator I (productSubtypePoint I a baseY) z * f z)) = _
  rw [← productTruncatedPairing_sum_right]
  congr 1
  funext z
  exact productFiberIndicator_partition I baseY f z

variable {Ω : Type*} [Fintype Ω] [∀ i, DecidableEq (X i)]

omit c in
theorem ProductCylinder.indicator_density_cut (d : ProductCylinder X)
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) :
    (fun z => productFiberIndicator d.1 (d.assignment base) z * observedProductDensity μ p F (d.cut F w) z) =
      observedProductDensity μ p F (d.cut F w) := by
  funext z
  by_cases hz : d.Contains z
  · have hi := (d.contains_iff base z).mp hz
    have he : productFiberIndicator d.1 (d.assignment base) z = 1 := by
      unfold productFiberIndicator
      exact if_pos hi
    rw [he, one_mul]
  · simp only [d.density_cut, if_neg hz, mul_zero]

theorem ProductCylinder.truncated_pairing_atoms (d : ProductCylinder X)
    (D : Finset (Finset ι)) (base : ∀ i, X i) (baseY : ∀ i, Y i)
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (w : Ω → ℝ) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (observedProductDensity μ p F (d.cut F w)) f =
      ∑ a : ∀ i : d.1, Y i, productAtomTruncatedPairing c D d.1 (d.assignment base)
        (productSubtypePoint d.1 a baseY) (observedProductDensity μ p F (d.cut F w)) f := by
  rw [productTruncatedPairing_atom_sum_right, d.indicator_density_cut μ base p F w]

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem observedProductDensity_residual_difference
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (hμ : ∀ i x, 0 < (μ i).weight x) (base : ∀ i, X i) (v : Ω → ℝ)
    {η τ H G a : ℝ} (ha : 0 ≤ a) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (hη : 0 ≤ η)
    (hmass : p.mean v ≤ τ) (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν D h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν D g) ≤ G) :
    |productTruncatedPairing c D (observedProductDensity μ p F v) (fun y => h y - a * g y)| ≤
      Real.sqrt (3 * τ) * (H + a * G) := by
  have hH := observedProductDensity_small_mass_pairing c p F hμ base v hv hη hmass D hcard hclose herr h hh
  have hG := observedProductDensity_small_mass_pairing c p F hμ base v hv hη hmass D hcard hclose herr g hg
  rw [productTruncatedPairing_sub_smul_right, sub_eq_add_neg]
  calc
    _ ≤ |productTruncatedPairing c D (observedProductDensity μ p F v) h| +
        |-(a * productTruncatedPairing c D (observedProductDensity μ p F v) g)| := abs_add_le _ _
    _ = |productTruncatedPairing c D (observedProductDensity μ p F v) h| +
        a * |productTruncatedPairing c D (observedProductDensity μ p F v) g| := by
      rw [abs_neg, abs_mul, abs_of_nonneg ha]
    _ ≤ Real.sqrt (3 * τ) * H + a * (Real.sqrt (3 * τ) * G) :=
      add_le_add hH (mul_le_mul_of_nonneg_left hG ha)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.retained_pairing_sum_le
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (D : Finset (Finset ι)) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z) {C : ℝ} (hC : 0 ≤ C)
    (E : (d : ProductCylinder X) → (Ω → ℝ) → (∀ i : d.1, Y i) → ℝ)
    (f : (∀ i, Y i) → ℝ)
    (hret : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ a : ∀ i : cf.1.1, Y i,
      productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 a baseY) (observedProductDensity μ p F cf.2) f ≤
      C * (productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) + E cf.1 cf.2 a) :
    ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ a : ∀ i : cf.1.1, Y i, productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 a baseY) (observedProductDensity μ p F cf.2) f)).sum ≤
      C + ((cs.zip (removedCylinderWeights F w cs)).map
        (fun cf => ∑ a : ∀ i : cf.1.1, Y i, E cf.1 cf.2 a)).sum := by
  apply list_weighted_error_sum_le _ _
    (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
      productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 a baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) _ hC
  · exact CylinderRemovalChain.joint_mass_sum_le_one c hchain hμ baseY hw hv
  · intro cf hcf
    have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (∀ i : cf.1.1, Y i))) => hret cf hcf a)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {X Y : I → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
    (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i)) (e : J ↪ I)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i)

include baseX baseY

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.truncated_pairing_decomposition
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (D : Finset (Finset ι)) (baseY : ∀ i, Y i) (f : (∀ i, Y i) → ℝ) :
    productTruncatedPairing c D (observedProductDensity μ p F w) f =
      ((cs.zip (removedCylinderWeights F w cs)).map
        (fun cf => ∑ a : ∀ i : cf.1.1, Y i,
          productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
            (productSubtypePoint cf.1.1 a baseY) (observedProductDensity μ p F cf.2) f)).sum +
      productTruncatedPairing c D (observedProductDensity μ p F v) f := by
  induction hchain with
  | nil => simp only [removedCylinderWeights, List.zip_nil_left, List.map_nil, List.sum_nil, zero_add]
  | @cons w v cs d hsize hmass hbounded rest ih =>
    have he : observedProductDensity μ p F w =
        (fun z => observedProductDensity μ p F (d.cut F w) z + observedProductDensity μ p F (d.erase F w) z) := by
      funext z
      have h := observedProductDensity_add μ p F (d.cut F w) (d.erase F w) z
      rw [show (fun z => d.cut F w z + d.erase F w z) = w from funext (d.cut_add_erase F w)] at h
      exact h
    rw [he, productTruncatedPairing_add_left, d.truncated_pairing_atoms c D base baseY p F w f, ih]
    simp only [removedCylinderWeights, List.zip_cons_cons, List.map_cons, List.sum_cons, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.total_pairing_le
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (D : Finset (Finset ι)) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (hmass : p.mean v ≤ τ)
    {η C H G a : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C) (ha : 0 ≤ a)
    {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν D h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν D g) ≤ G)
    (E : (d : ProductCylinder X) → (Ω → ℝ) → (∀ i : d.1, Y i) → ℝ)
    (hret : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ z : ∀ i : cf.1.1, Y i,
      productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 z baseY) (observedProductDensity μ p F cf.2) (fun y => h y - a * g y) ≤
      C * (productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 z baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) + E cf.1 cf.2 z) :
    productTruncatedPairing c D (observedProductDensity μ p F w) (fun y => h y - a * g y) ≤
      C + ((cs.zip (removedCylinderWeights F w cs)).map
        (fun cf => ∑ z : ∀ i : cf.1.1, Y i, E cf.1 cf.2 z)).sum +
      Real.sqrt (3 * τ) * (H + a * G) := by
  have hretained := CylinderRemovalChain.retained_pairing_sum_le c hchain hμ D baseY hw
    (fun z => (hv z).1) hC E (fun y => h y - a * g y) hret
  have hresidual := observedProductDensity_residual_difference c p F hμ base v ha hv hη hmass
    D hcard hclose herr h g hh hg
  rw [CylinderRemovalChain.truncated_pairing_decomposition c hchain D baseY]
  exact add_le_add hretained ((le_abs_self _).trans hresidual)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem CylinderRemovalChain.total_pairing_with_shell_budget
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ : ℝ} {j r : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (D : Finset (Finset ι)) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) (hmass : p.mean v ≤ τ)
    {η C H G a κ ε P : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hε : 0 < ε)
    {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν D h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν D g) ≤ G)
    (B : (d : ProductCylinder X) → (Ω → ℝ) → (∀ i : d.1, Y i) → ℝ)
    (hB : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ z, 0 ≤ B cf.1 cf.2 z)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map
      (fun cf => ∑ z : ∀ i : cf.1.1, Y i, B cf.1 cf.2 z)).sum ≤ Real.exp P)
    (hb : j + CyclicCrootSisask.spectralIterations ε P ≤ b)
    (hret : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ z : ∀ i : cf.1.1, Y i,
      productAtomTruncatedPairing c D cf.1.1 (cf.1.assignment base)
        (productSubtypePoint cf.1.1 z baseY) (observedProductDensity μ p F cf.2) (fun y => h y - a * g y) ≤
      C * (productCouplingAtomMass c cf.1.1 (cf.1.assignment base) (productSubtypePoint cf.1.1 z baseY) *
        cf.1.mass μ base (observedProductDensity μ p F cf.2)) +
      κ ^ (b - cf.1.1.card) * B cf.1 cf.2 z) :
    productTruncatedPairing c D (observedProductDensity μ p F w) (fun y => h y - a * g y) ≤
      C + ε / 16 + Real.sqrt (3 * τ) * (H + a * G) := by
  let E := fun (d : ProductCylinder X) (f : Ω → ℝ) (z : ∀ i : d.1, Y i) =>
    κ ^ (b - d.1.card) * B d f z
  have ht := CylinderRemovalChain.total_pairing_le c hchain hμ D baseY hw hv hmass
    hη hC ha hcard hclose herr h g hh hg E hret
  have hs := list_dependent_shell_sum_after_cutoff (cs.zip (removedCylinderWeights F w cs))
    (fun cf => ∀ i : cf.1.1, Y i) (fun cf => cf.1.1.card)
    (fun cf z => E cf.1 cf.2 z) (fun cf z => B cf.1 cf.2 z)
    hε hκ0 hκhalf (fun cf hcf => (hchain.removed_size_mass cf hcf).1)
    hB (fun _ _ _ => le_rfl) hbudget hb
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem weighted_pairing_error_compose {P Q R m E F : ℝ} (hm : 0 ≤ m)
    (hP : |P - m * Q| ≤ E) (hQ : |Q - R| ≤ F) : |P - m * R| ≤ E + m * F := by
  calc
    _ = |(P - m * Q) + m * (Q - R)| := by congr 1; ring
    _ ≤ |P - m * Q| + |m * (Q - R)| := abs_add_le _ _
    _ = |P - m * Q| + m * |Q - R| := by rw [abs_mul, abs_of_nonneg hm]
    _ ≤ _ := add_le_add hP (mul_le_mul_of_nonneg_left hQ hm)

theorem productKernel_conditioned_mean_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (productSectionAverage μ I I x w)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (productSectionAverage ν I I y f)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (productSectionAverage μ I I x w)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y *
        ((FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I x w) *
         (FiniteProbabilityWeights.pi ν).mean (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hsub : lowDegreeCoordinateSets ι (b - I.card) ⊆ lowDegreeCoordinateSets ι b := by
    intro S hS
    exact (mem_lowDegreeCoordinateSets ι b S).mpr
      (((mem_lowDegreeCoordinateSets ι (b - I.card) S).mp hS).trans (Nat.sub_le b I.card))
  have hcore := productKernel_core_comparison μ ν K C hC hbound hK Iᶜ hr hκ0 hκ1
    (fun i hi => hcap i (Finset.mem_compl.mp hi)) hsmall
    (productSectionAverage μ I I x w) (productSectionAverage ν I I y f) hw hf
    ((Real.sqrt_le_sqrt (productANOVAEnergy_mono μ hsub _)).trans hM)
    ((Real.sqrt_le_sqrt (productANOVAEnergy_mono ν hsub _)).trans hN)
  have hshell := productKernel_conditioning_shell_of_truncated μ ν K C hC hbound hK I b hIb
    hκ0 hκ1 hcap x y w f hM hN
  exact weighted_pairing_error_compose (productCouplingAtomMass_nonneg c I x y) hshell hcore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_scaled_conditioned_mean_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N m s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w f -
      productCouplingAtomMass c I x y *
        (productConditionalMean μ I w x * productConditionalMean ν I f y)| ≤
      m * s * ((2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N)) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  have hw_eq : productSectionAverage μ I I x (fun z => m⁻¹ * w z) =
      (fun z => m⁻¹ * productSectionAverage μ I I x w z) :=
    funext (productSectionAverage_smul μ I I x m⁻¹ w)
  have hf_eq : productSectionAverage ν I I y (fun z => s⁻¹ * f z) =
      (fun z => s⁻¹ * productSectionAverage ν I I y f z) :=
    funext (productSectionAverage_smul ν I I y s⁻¹ f)
  have h := productKernel_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hκ0 hκ1 hcap hsmall x y (fun z => m⁻¹ * w z) (fun z => s⁻¹ * f z)
    (by simpa only [hw_eq] using hw) (by simpa only [hf_eq] using hf)
    (by simpa only [hw_eq] using hM) (by simpa only [hf_eq] using hN)
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y
      (fun z => m⁻¹ * w z) (fun z => s⁻¹ * f z) - productCouplingAtomMass c I x y *
      ((FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ I I x (fun z => m⁻¹ * w z)) *
       (FiniteProbabilityWeights.pi ν).mean (productSectionAverage ν I I y (fun z => s⁻¹ * f z)))| ≤ _ at h
  rw [productAtomTruncatedPairing_smul, productSectionAverage_self_mean, productSectionAverage_self_mean,
    productConditionalMean_smul, productConditionalMean_smul] at h
  exact normalized_pairing_error_scale hm hs h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCylinderTotal
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scaled_conditioned_error_rearrange {P a m s H E U : ℝ}
    (h : |P - a * (m * H)| ≤ m * s * (E + a * U)) :
    |P - (a * m) * H| ≤ m * s * E + a * m * s * U := by
  calc
    _ = |P - a * (m * H)| := by congr 1; ring
    _ ≤ _ := h
    _ = _ := by ring

theorem productKernel_retained_atom_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N m v τ lam ε ξ P : ℝ} (hm : 0 < m) (hv : 0 ≤ v) (hτ : 0 < τ)
    (hlam : 0 < lam) (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsmall : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) (hMN : M * N ≤ Real.exp P)
    (hrtail : CyclicCrootSisask.spectralIterations ξ P ≤ r)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (h g : (∀ i, Y i) → ℝ)
    (hmean : productConditionalMean μ I w x = m)
    (hHmean : productConditionalMean ν I h y ≤ lam * productConditionalMean ν I g y + lam * τ)
    (hGmean : v - τ ≤ productConditionalMean ν I g y)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ A ^ (2 * k))
    (hh : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν I I y h z)) ≤ B ^ (2 * k))
    (hg : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => (2 * (v + τ))⁻¹ * productSectionAverage ν I I y g z)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ M)
    (hNH : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν I I y h z)) ≤ N)
    (hNG : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => (2 * (v + τ))⁻¹ * productSectionAverage ν I I y g z)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w
      (fun z => h z - (1 + ε) * lam * g z) ≤
      (productCouplingAtomMass c I x y * m) * lam * (1 + 2 * ε) * τ +
        m * lam * (v + τ) * (6 + 2 * ε) * (2 : ℝ) ^ I.card * κ ^ (b - I.card) * M * N := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  let U := 2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N
  let E := (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N)
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans hM
  have hN0 : 0 ≤ N := (Real.sqrt_nonneg _).trans hNH
  have hcore := normalized_core_error_budget hξ hξ1 hκ0 hκhalf hM0 hN0 hMN hrtail hlow
  have hU : 4 * U ≤ ξ := hcore.2
  have hU' : 2 * U ≤ ξ := by linarith
  have hH := productKernel_scaled_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hm (by positivity : 0 < 4 * lam * (v + τ)) hκ0 (by linarith) hcap hcore.1
    x y w h hw hh hM hNH
  have hG := productKernel_scaled_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hm (by positivity : 0 < 2 * (v + τ)) hκ0 (by linarith) hcap hcore.1
    x y w g hw hg hM hNG
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w h -
    productCouplingAtomMass c I x y * (productConditionalMean μ I w x * productConditionalMean ν I h y)| ≤
      m * (4 * lam * (v + τ)) * (E + productCouplingAtomMass c I x y * U) at hH
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w g -
    productCouplingAtomMass c I x y * (productConditionalMean μ I w x * productConditionalMean ν I g y)| ≤
      m * (2 * (v + τ)) * (E + productCouplingAtomMass c I x y * U) at hG
  rw [hmean] at hH hG
  have hret := retained_atom_from_normalized_errors
    (productCouplingAtomMass_nonneg c I x y) hm.le hlam.le hv hτ.le hε
    (scaled_conditioned_error_rearrange hH) (scaled_conditioned_error_rearrange hG)
    hU hU' hHmean hGmean hsmall
  rw [productAtomTruncatedPairing_sub_smul_right]
  exact hret.trans_eq (by dsimp only [E]; ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.kernel_total_pairing_le {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {L τ : ℝ} {j r b : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F L τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    {κ A B M N v lam ε ξ P Q η shell H G : ℝ}
    (hM0 : 0 ≤ M) (hN0 : 0 ≤ N) (hv : 0 ≤ v) (hτ : 0 < τ) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hsmall : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) (hMN : M * N ≤ Real.exp P)
    (hrtail : CyclicCrootSisask.spectralIterations ξ P ≤ r) (hrb : j + r ≤ b)
    (hη : 0 ≤ η)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) g) ≤ G)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell Q ≤ b)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * lam * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * M * N))).sum ≤ Real.exp Q)
    (hpieces : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      let m := cf.1.mass μ base (observedProductDensity μ p F cf.2)
      let x := cf.1.assignment base
      let W := observedProductDensity μ p F cf.2
      (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (fun z => m⁻¹ * productSectionAverage μ cf.1.1 cf.1.1 x W z)) ≤ A ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
        (fun z => m⁻¹ * productSectionAverage μ cf.1.1 cf.1.1 x W z)) ≤ M ∧
      ∀ z : ∀ i : cf.1.1, Y i,
        let y := productSubtypePoint cf.1.1 z baseY
        productConditionalMean ν cf.1.1 h y ≤ lam * productConditionalMean ν cf.1.1 g y + lam * τ ∧
        v - τ ≤ productConditionalMean ν cf.1.1 g y ∧
        (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
          (fun a => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y h a)) ≤ B ^ (2 * k)) ∧
        (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
          (fun a => (2 * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y g a)) ≤ B ^ (2 * k)) ∧
        Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
          (fun a => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y h a)) ≤ N ∧
        Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
          (fun a => (2 * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y g a)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets ι b) (observedProductDensity μ p F w)
      (fun z => h z - (1 + ε) * lam * g z) ≤
      lam * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (H + (1 + ε) * lam * G) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  let pref := fun (d : ProductCylinder X) (f : Ω → ℝ) (_z : ∀ i : d.1, Y i) =>
    d.mass μ base (observedProductDensity μ p F f) * lam * (v + τ) * (6 + 2 * ε) *
      (2 : ℝ) ^ d.1.card * M * N
  apply CylinderRemovalChain.total_pairing_with_shell_budget c hchain hμ _ baseY hw hrem hmass
    hη (by positivity) (by positivity) hκ0 hκhalf hshell
    (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS) hclose herr h g hh hg pref
  · intro cf hcf z
    have hm := hτ.trans (hchain.removed_size_mass cf hcf).2
    dsimp only [pref]
    positivity
  · simpa only [pref, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hbudget
  · exact hb
  · intro cf hcf z
    obtain ⟨hsize, hmass'⟩ := hchain.removed_size_mass cf hcf
    obtain ⟨hwl, hwm, hsite⟩ := hpieces cf hcf
    obtain ⟨hHm, hGm, hhl, hgl, hhn, hgn⟩ := hsite z
    have hp := productKernel_retained_atom_comparison μ ν K C hC hbound hK cf.1.1
      (by omega) (by omega) (hτ.trans hmass') hv hτ hlam hε hξ hξ1 hsmall hκ0 hκhalf
      (fun i _ => hcap i) hlow hMN hrtail (cf.1.assignment base)
      (productSubtypePoint cf.1.1 z baseY) (observedProductDensity μ p F cf.2) h g rfl
      hHm hGm hwl hhl hgl hwm hhn hgn
    exact hp.trans_eq (by dsimp only [pref]; ring)

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.CylinderRemovalChain.kernel_total_pairing_le.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.CylinderRemovalChain.kernel_total_pairing_le.{u_1, u_2, u_3, u_4}
