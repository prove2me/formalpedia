-- Prove2me | solution 1 for OAI.Erdos3.CylinderRemovalChain.uniform_section_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:24:13.204977+00:00
-- url     : https://prove2.me/submissions/cd204e3e-758e-46bf-ace1-bbceec97301e

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B094
import Theorems.Thm_OAI_Erdos3_productANOVATensor_uniform_of_normalized
import Theorems.Thm_OAI_Erdos3_productANOVA_weighted_lp_of_sections

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ApproxMomentEnvelope
namespace OAI

section

namespace Erdos3

theorem approxMomentEnvelope_one_le (N r : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    1 ≤ approxMomentEnvelope N r M := by
  unfold approxMomentEnvelope
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (one_le_pow₀ (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith))
  · linarith

theorem approxMomentEnvelope_mono (N : ℕ) {s r : ℕ} (hsr : s ≤ r) {M : ℝ} (hM : 0 ≤ M) :
    approxMomentEnvelope N s M ≤ approxMomentEnvelope N r M := by
  unfold approxMomentEnvelope
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hsr 1))
    (pow_le_pow_right₀ (by have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) hsr) (by positivity) (by positivity)

theorem approxMomentEnvelope_bounds_term (N k : ℕ) {M eta : ℝ} (hM : 0 ≤ M) (heta : eta ≤ 1) :
    (2 : ℝ) ^ k * (N : ℝ) ^ k * M * (1 + eta) ≤ approxMomentEnvelope N k M := by
  calc
    _ ≤ (2 : ℝ) ^ k * (N : ℝ) ^ k * M * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ (2 : ℝ) ^ k * (2 + (N : ℝ)) ^ k * (2 + M) * 2 := by gcongr <;> linarith
    _ = approxMomentEnvelope N k M := by unfold approxMomentEnvelope; rw [pow_succ]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ApproxMomentBudget
namespace OAI

section

namespace Erdos3

theorem approxMomentBudget_eta_le_half (N r q : ℕ) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) : eta ≤ 1 / 2 := by
  have hpow : 1 ≤ approxMomentEnvelope N r M ^ q := one_le_pow₀ (approxMomentEnvelope_one_le N r hM)
  have h : eta ≤ eta * approxMomentEnvelope N r M ^ q := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow heta
  exact h.trans hbudget

theorem approxMomentBudget_mono (N q : ℕ) {s r : ℕ} (hsr : s ≤ r) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) :
    eta * approxMomentEnvelope N s M ^ q ≤ 1 / 2 := by
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (zero_le_one.trans (approxMomentEnvelope_one_le N s hM))
    (approxMomentEnvelope_mono N hsr hM) q) heta).trans hbudget

theorem approxMomentBudget_error_le_one (N q : ℕ) {k r : ℕ} (hkr : k ≤ r) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) :
    eta * ((2 : ℝ) ^ k * (N : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1 := by
  have he := approxMomentBudget_eta_le_half N r q hM heta hbudget
  have hterm := (approxMomentEnvelope_bounds_term N k hM (by linarith : eta ≤ 1)).trans
    (approxMomentEnvelope_mono N hkr hM)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hterm q) heta).trans
    (hbudget.trans (by norm_num))

theorem approxMomentBudget_of_small (N r q : ℕ) {M eta : ℝ} (hM : 0 ≤ M)
    (hsmall : eta ≤ (1 / 2) * (approxMomentEnvelope N r M ^ q)⁻¹) :
    eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2 := by
  have hp : 0 < approxMomentEnvelope N r M := lt_of_lt_of_le zero_lt_one (approxMomentEnvelope_one_le N r hM)
  have h := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hp.le q)
  simpa only [mul_assoc, inv_mul_cancel₀ (pow_pos hp q).ne', mul_one] using h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ApproxMomentCutoff
namespace OAI

section

namespace Erdos3

theorem approx_section_cutoff {a j r q : ℕ} (haj : a ≤ j) (hjr : j ≤ r) :
    (r - j) * (q + 1) ≤ r * (q + 1) - a := by
  apply Nat.le_sub_of_add_le
  have hmul : a ≤ j * (q + 1) := by nlinarith
  calc
    (r - j) * (q + 1) + a ≤ (r - j) * (q + 1) + j * (q + 1) := Nat.add_le_add_left hmul _
    _ = r * (q + 1) := by rw [← Nat.add_mul, Nat.sub_add_cancel hjr]

theorem approx_moment_cutoff {k r q : ℕ} (hkr : k ≤ r) : q * k ≤ r * (q + 1) := by
  have h := Nat.mul_le_mul_left q hkr
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSectionPermutation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedMoment_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℝ) (f : X → ℝ) : 0 ≤ ∑ x, w x * |f x| ^ p :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (Real.rpow_nonneg (abs_nonneg _) _))

theorem finiteWeightedLp_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : ℝ) (f : X → ℝ) : 0 ≤ finiteWeightedLp w p f :=
  Real.rpow_nonneg (finiteWeightedMoment_nonneg w hw p f) _

theorem finiteWeightedLp_smul (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c) (f : X → ℝ) :
    finiteWeightedLp w p (fun x => c * f x) = c * finiteWeightedLp w p f := by
  have hm : (∑ x, w x * |c * f x| ^ p) = c ^ p * ∑ x, w x * |f x| ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
    ring
  unfold finiteWeightedLp
  rw [hm, Real.mul_rpow (Real.rpow_nonneg hc _) (finiteWeightedMoment_nonneg w hw p f),
    ← Real.rpow_mul hc]
  have he : p * (1 / p) = 1 := by field_simp
  rw [he, Real.rpow_one]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_rpow_self (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f : X → ℝ) :
    finiteWeightedLp w p f ^ p = ∑ x, w x * |f x| ^ p := by
  unfold finiteWeightedLp
  rw [one_div, Real.rpow_inv_rpow (finiteWeightedMoment_nonneg w hw p f) hp.ne']

theorem finiteWeightedLp_zero_support (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {p : ℝ} (hp : 0 < p) (f : X → ℝ) (h : finiteWeightedLp w p f = 0)
    (x : X) (hx : w x ≠ 0) : f x = 0 := by
  have hm : (∑ x, w x * |f x| ^ p) = 0 := by
    rw [← finiteWeightedLp_rpow_self w hw hp f, h, Real.zero_rpow hp.ne']
  have ht : w x * |f x| ^ p = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => mul_nonneg (hw y) (Real.rpow_nonneg (abs_nonneg _) _))).mp hm x (Finset.mem_univ x)
  have ha : |f x| ^ p = 0 := (mul_eq_zero.mp ht).resolve_left hx
  exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp ha)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

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

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω J L : Type*} [Fintype Ω]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteWeightedConjugate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeighted_conjugate_lp_exp_bound (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (q : ℝ) (hq : 1 < q)
    (f : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfcap : ∀ x, f x ≤ Real.exp q)
    (hm : (∑ x, w x * f x) ≤ 1) :
    finiteWeightedLp w (q / (q - 1)) f ≤ Real.exp 1 := by
  let s := q / (q - 1)
  have hq1 : 0 < q - 1 := by linarith
  have hs : 0 < s := div_pos (by linarith) hq1
  have hs1 : 0 ≤ s - 1 := by
    dsimp [s]
    have h : 1 ≤ q / (q - 1) := (le_div_iff₀ hq1).mpr (by linarith)
    linarith
  have he : q * (s - 1) = s := by
    dsimp [s]
    field_simp
    ring
  have hp (x : X) : |f x| ^ s ≤ (Real.exp 1) ^ s * f x := by
    rw [abs_of_nonneg (hf0 x)]
    calc
      f x ^ s = f x ^ (s - 1) * f x := by
        simpa only [sub_add_cancel] using
          Real.rpow_add_one' (hf0 x) (show s - 1 + 1 ≠ 0 by linarith)
      _ ≤ (Real.exp q) ^ (s - 1) * f x :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hf0 x) (hfcap x) hs1) (hf0 x)
      _ = (Real.exp 1) ^ s * f x := by
        rw [← Real.exp_mul, he, ← Real.exp_mul, one_mul]
  apply (Real.rpow_le_rpow_iff (finiteWeightedLp_nonneg w hw s f)
    (Real.exp_pos 1).le hs).mp
  rw [finiteWeightedLp_rpow_self w hw hs f]
  calc
    (∑ x, w x * |f x| ^ s) ≤ ∑ x, w x * ((Real.exp 1) ^ s * f x) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hp x) (hw x))
    _ = (Real.exp 1) ^ s * (∑ x, w x * f x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ (Real.exp 1) ^ s := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (Real.exp_pos 1).le s)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_ne_zero (p : FiniteProbabilityWeights Ω) : ∃ x, p.weight x ≠ 0 := by
  obtain ⟨x, hx⟩ := p.exists_weight_pos
  exact ⟨x, hx.ne'⟩

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

variable {X : Type*} [Fintype X]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

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

theorem productCoordinateMix_weight_ne_zero (μ : ∀ i, FiniteProbabilityWeights (X i))
    (T : Finset I) (z x : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (hx : (FiniteProbabilityWeights.pi μ).weight x ≠ 0) :
    (FiniteProbabilityWeights.pi μ).weight (productCoordinateMix T z x) ≠ 0 := by
  have h := mul_ne_zero hz hx
  rw [← productCoordinateMix_weight μ T z x] at h
  exact (mul_ne_zero_iff.mp h).1

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

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

end Erdos3

end

section

namespace Erdos3

variable {n k : ℕ}

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

theorem finiteWeightedHolder_normalized (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) (hnorm : ∀ i, (∑ x, w x * |f i x| ^ p i) ≤ 1) :
    (∑ x, w x * ∏ i, |f i x|) ≤ 1 := by
  have hpoint (x : X) : (∏ i, |f i x|) ≤ ∑ i, (1 / p i) * |f i x| ^ p i := by
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun i => 1 / p i)
      (fun i => |f i x| ^ p i) (fun i _ => le_of_lt (one_div_pos.mpr (hp i))) hsum
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
    have he (i : I) : (|f i x| ^ p i) ^ (1 / p i) = |f i x| := by
      rw [← Real.rpow_mul (abs_nonneg _)]
      have hc : p i * (1 / p i) = 1 := by field_simp [(hp i).ne' ]
      rw [hc, Real.rpow_one]
    simpa only [he] using h
  calc
    (∑ x, w x * ∏ i, |f i x|) ≤ ∑ x, w x * ∑ i, (1 / p i) * |f i x| ^ p i :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
    _ = ∑ i, (1 / p i) * ∑ x, w x * |f i x| ^ p i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ ∑ i, 1 / p i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hnorm i) (le_of_lt (one_div_pos.mpr (hp i)))
    _ = 1 := hsum

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I X : Type*} [Fintype I] [Fintype X]

theorem finiteWeightedHolder (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) :
    (∑ x, w x * ∏ i, |f i x|) ≤ ∏ i, finiteWeightedLp w (p i) (f i) := by
  classical
  by_cases hz : ∃ i, finiteWeightedLp w (p i) (f i) = 0
  · obtain ⟨i, hi⟩ := hz
    have hleft : (∑ x, w x * ∏ j, |f j x|) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : w x = 0
      · rw [hx, zero_mul]
      · have hix := finiteWeightedLp_zero_support w hw (hp i) (f i) hi x hx
        have hprod : (∏ j, |f j x|) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hix, abs_zero])
        rw [hprod, mul_zero]
    rw [hleft]
    exact Finset.prod_nonneg (fun j _ => finiteWeightedLp_nonneg w hw (p j) (f j))
  · push Not at hz
    let M : I → ℝ := fun i => finiteWeightedLp w (p i) (f i)
    have hM : ∀ i, 0 < M i := fun i =>
      lt_of_le_of_ne (finiteWeightedLp_nonneg w hw (p i) (f i)) (Ne.symm (hz i))
    let g : I → X → ℝ := fun i x => (M i)⁻¹ * f i x
    have hg (i : I) : finiteWeightedLp w (p i) (g i) = 1 := by
      change finiteWeightedLp w (p i) (fun x => (M i)⁻¹ * f i x) = 1
      rw [finiteWeightedLp_smul w hw (hp i) (inv_nonneg.mpr (hM i).le)]
      exact inv_mul_cancel₀ (hM i).ne'
    have hnorm (i : I) : (∑ x, w x * |g i x| ^ p i) ≤ 1 := by
      rw [← finiteWeightedLp_rpow_self w hw (hp i) (g i), hg, Real.one_rpow]
    have hnormal := finiteWeightedHolder_normalized w hw p hp hsum g hnorm
    have hpoint (i : I) (x : X) : |f i x| = M i * |g i x| := by
      dsimp [g]
      rw [abs_mul, abs_inv, abs_of_pos (hM i), ← mul_assoc,
        mul_inv_cancel₀ (hM i).ne', one_mul]
    have hprod (x : X) : (∏ i, |f i x|) = (∏ i, M i) * ∏ i, |g i x| := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => hpoint i x)
    calc
      (∑ x, w x * ∏ i, |f i x|) = (∏ i, M i) * ∑ x, w x * ∏ i, |g i x| := by
        simp_rw [hprod]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ∏ i, M i := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hnormal
          (Finset.prod_nonneg (fun i _ => (hM i).le))
      _ = _ := rfl

theorem finiteWeightedHolder_abs (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, 1 / p i) = 1)
    (f : I → X → ℝ) :
    |∑ x, w x * ∏ i, f i x| ≤ ∏ i, finiteWeightedLp w (p i) (f i) := by
  calc
    |∑ x, w x * ∏ i, f i x| ≤ ∑ x, |w x * ∏ i, f i x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x * ∏ i, |f i x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hw x), Finset.abs_prod]
    _ ≤ _ := finiteWeightedHolder w hw p hp hsum f

end Erdos3

end

section

namespace Erdos3

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedHolder_pair (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1)
    (f g : X → ℝ) :
    |∑ x, w x * (f x * g x)| ≤ finiteWeightedLp w p f * finiteWeightedLp w q g := by
  have h := finiteWeightedHolder_abs w hw (fun b : Bool => cond b p q)
    (fun b => by cases b <;> assumption) (by simpa [add_comm] using hpq)
    (fun b x => cond b (f x) (g x))
  simpa [mul_comm] using h

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

variable {X : Type*} [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X] [Nonempty X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J X : Type*} [Fintype J] [DecidableEq J] [Fintype X]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {J B X : Type*} [Fintype J] [DecidableEq J]
  [Fintype B] [DecidableEq B] [Fintype X]

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

theorem productCoordinateMix_section (T A B : Finset I) (hAT : A ⊆ T)
    (z x y v : ∀ i, X i) :
    productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y) =
      productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x)
        (productCoordinateMix Tᶜ y v) := by
  funext i
  by_cases hiT : i ∈ T
  · by_cases hiA : i ∈ A <;> simp [productCoordinateMix, hiT, hiA]
  · have hiA : i ∉ A := fun h => hiT (hAT h)
    by_cases hiB : i ∈ B <;> simp [productCoordinateMix, hiT, hiA, hiB]

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

theorem productSectionAverage_nonneg (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (hf : ∀ x, 0 ≤ f x) (x : ∀ i, X i) :
    0 ≤ productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => hf _)

theorem productConditionalMean_sectionAverage (T A B : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productConditionalMean μ B (productSectionAverage μ T A z f) x =
      productConditionalMean μ (A ∪ (B \ T)) f (productCoordinateMix T z x) := by
  change (FiniteProbabilityWeights.pi μ).mean (fun y => (FiniteProbabilityWeights.pi μ).mean
    (fun v => f (productCoordinateMix T (productCoordinateMix A z v) (productCoordinateMix B x y)))) = _
  simp_rw [productCoordinateMix_section T A B hAT]
  exact productMean_coordinateMix μ Tᶜ
    (fun v => f (productCoordinateMix (A ∪ (B \ T)) (productCoordinateMix T z x) v))

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

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSectionAverage_mono (T A : Finset I) (z : ∀ i, X i)
    (f g : (∀ i, X i) → ℝ) (h : ∀ x, f x ≤ g x) (x : ∀ i, X i) :
    productSectionAverage μ T A z f x ≤ productSectionAverage μ T A z g x :=
  (FiniteProbabilityWeights.pi μ).mean_mono (fun _ => h _)

theorem productSectionAverage_smul (T A : Finset I) (z : ∀ i, X i) (c : ℝ)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productSectionAverage μ T A z (fun y => c * f y) x = c * productSectionAverage μ T A z f x :=
  (FiniteProbabilityWeights.pi μ).mean_const_mul c _

theorem productSectionAverage_weighted_cap (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    0 ≤ productSectionAverage μ T A z (fun y => rho y * F y) x ∧
      productSectionAverage μ T A z (fun y => rho y * F y) x ≤
        M * productSectionAverage μ T A z rho x := by
  constructor
  · exact productSectionAverage_nonneg μ T A z _ (fun y => mul_nonneg (hrho y) (hF y).1) x
  · calc
      _ ≤ productSectionAverage μ T A z (fun y => M * rho y) x :=
        productSectionAverage_mono μ T A z _ _ (fun y => by
          simpa only [mul_comm M] using mul_le_mul_of_nonneg_left (hF y).2 (hrho y)) x
      _ = _ := productSectionAverage_smul μ T A z M rho x

theorem productSectionAverage_weighted_zero (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i)
    (hz : productSectionAverage μ T A z rho x = 0) :
    productSectionAverage μ T A z (fun y => rho y * F y) x = 0 := by
  have h := productSectionAverage_weighted_cap μ T A z rho F hrho hF x
  rw [hz, mul_zero] at h
  exact le_antisymm h.2 h.1

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productNormalizedSection_boundedMarginals (T A : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {K : ℝ} (hK : 1 ≤ K) {r : ℕ} (hAr : A.card ≤ r)
    (f : (∀ i, X i) → ℝ) (hf : ProductBoundedMarginals μ f K r) :
    ProductBoundedMarginals μ (productNormalizedSection μ T A z K f) K (r - A.card) := by
  intro J hJ x hx
  change productConditionalMean μ J (fun y => (K ^ A.card)⁻¹ * productSectionAverage μ T A z f y) x ≤ _
  rw [productConditionalMean_smul, productConditionalMean_sectionAverage μ T A J hAT]
  have hdis : Disjoint A (J \ T) := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiD
    exact (Finset.mem_sdiff.mp hiD).2 (hAT hiA)
  have hcard : (A ∪ (J \ T)).card ≤ r := by
    rw [Finset.card_union_of_disjoint hdis]
    have hj := Finset.card_le_card (Finset.sdiff_subset : J \ T ⊆ J)
    omega
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hp : K ^ A.card ≠ 0 := (pow_pos hKpos _).ne'
  have hbound := hf (A ∪ (J \ T)) hcard (productCoordinateMix T z x)
    (productCoordinateMix_weight_ne_zero μ T z x hz hx)
  calc
    (K ^ A.card)⁻¹ * productConditionalMean μ (A ∪ (J \ T)) f (productCoordinateMix T z x)
        ≤ (K ^ A.card)⁻¹ * K ^ (A ∪ (J \ T)).card :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (pow_nonneg hKpos.le _))
    _ = K ^ (J \ T).card := by
      rw [Finset.card_union_of_disjoint hdis, pow_add, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    _ ≤ K ^ J.card := pow_le_pow_right₀ hK (Finset.card_le_card Finset.sdiff_subset)

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

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

theorem ProductMarginalsClose.section {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (T A : Finset I) (hAT : A ⊆ T)
    (hAs : A.card ≤ s) (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) :
    ProductMarginalsClose μ (productSectionAverage μ T A z rho) eta (s - A.card) := by
  intro B hB x hx
  rw [productConditionalMean_sectionAverage μ T A B hAT]
  apply h
  · have hcard := Finset.card_union_le A (B \ T)
    have hdiff := Finset.card_le_card (Finset.sdiff_subset : B \ T ⊆ B)
    omega
  · exact productCoordinateMix_weight_ne_zero μ T z x hz hx

theorem ProductBoundedMarginals.mono {f : (∀ i, X i) → ℝ} {K : ℝ} {r s : ℕ}
    (h : ProductBoundedMarginals μ f K r) (hs : s ≤ r) : ProductBoundedMarginals μ f K s :=
  fun B hB x hx => h B (hB.trans hs) x hx

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

theorem productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D (fun y => c * f y) = c ^ 2 * productANOVAEnergy μ D f := by
  simp only [productANOVAEnergy, productANOVA_smul, mul_pow,
    FiniteProbabilityWeights.mean_const_mul, Finset.mul_sum]

theorem sqrt_productANOVAEnergy_smul (D : Finset (Finset I)) (c : ℝ) (f : (∀ i, X i) → ℝ) :
    Real.sqrt (productANOVAEnergy μ D (fun y => c * f y)) =
      |c| * Real.sqrt (productANOVAEnergy μ D f) := by
  rw [productANOVAEnergy_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ANOVABootstrapInequality
namespace OAI

section

namespace Erdos3

theorem anova_bootstrap_le {U D E : ℝ} (_hU : 0 ≤ U) (hD : 0 ≤ D) (hE : E ≤ D)
    (h : U ^ 2 ≤ D * max U E) : U ≤ D := by
  by_cases hUE : U ≤ E
  · rw [max_eq_right hUE] at h
    have hm := mul_le_mul_of_nonneg_left hE hD
    nlinarith
  · rw [max_eq_left (le_of_not_ge hUE)] at h
    nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ApproxANOVAMomentScale
namespace OAI

section

namespace Erdos3

theorem anova_moment_coefficient {k : ℕ} (hk : 0 < k) {n R : ℝ}
    (hn : 0 ≤ n) (h : 4 * n ≤ R ^ 2) :
    Real.exp 1 * n ^ k ≤ R ^ (2 * k) := by
  have he : Real.exp 1 ≤ (4 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
  have hpow : (4 : ℝ) ≤ 4 ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hk
  calc
    Real.exp 1 * n ^ k ≤ 4 ^ k * n ^ k :=
      mul_le_mul_of_nonneg_right (he.trans hpow) (pow_nonneg hn _)
    _ = (4 * n) ^ k := (mul_pow _ _ _).symm
    _ ≤ (R ^ 2) ^ k := pow_le_pow_left₀ (mul_nonneg (by norm_num) hn) h k
    _ = R ^ (2 * k) := (pow_mul _ _ _).symm

theorem anova_moment_scale {K p : ℝ} (hK : 1 ≤ K) (hp : 0 ≤ p)
    {q k : ℕ} (hk : 0 < k) (hkP : (k : ℝ) ≤ p) (hqP : (q : ℝ) ≤ p + 2) :
    Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ (4 * (1 + K) * (p + 2)) ^ (2 * k) := by
  apply anova_moment_coefficient hk (by positivity)
  have hprod : ((q * k : ℕ) : ℝ) ≤ (p + 2) ^ 2 := by
    rw [Nat.cast_mul]
    have h := mul_le_mul hqP (show (k : ℝ) ≤ p + 2 by linarith)
      (by positivity : 0 ≤ (k : ℝ)) (by linarith : 0 ≤ p + 2)
    nlinarith
  have hR : 2 * (p + 2) ≤ 4 * (1 + K) * (p + 2) := by nlinarith
  nlinarith [sq_nonneg (4 * (1 + K) * (p + 2) - 2 * (p + 2))]

end Erdos3

end

section

namespace Erdos3

theorem approx_anova_moment_scale {K p : ℝ} (hK : 1 ≤ K) (hp : 0 ≤ p)
    {q k : ℕ} (hk : 0 < k) (hkP : (k : ℝ) ≤ p) (hqP : (q : ℝ) ≤ p + 2) :
    2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ (8 * (1 + K) * (p + 2)) ^ (2 * k) := by
  let D := 4 * (1 + K) * (p + 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htwo : (2 : ℝ) ≤ 2 ^ (2 * k) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ 2 * k)
  calc
    _ = 2 * (Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k) := by ring
    _ ≤ 2 * D ^ (2 * k) := mul_le_mul_of_nonneg_left (anova_moment_scale hK hp hk hkP hqP) (by norm_num)
    _ ≤ 2 ^ (2 * k) * D ^ (2 * k) := mul_le_mul_of_nonneg_right htwo (pow_nonneg hD _)
    _ = (2 * D) ^ (2 * k) := (mul_pow _ _ _).symm
    _ = _ := by congr 1; dsimp [D]; ring

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

theorem productSectionDensityWeight_nonneg (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x)
    (x : ∀ i, X i) : 0 ≤ productSectionDensityWeight μ T A z rho F x := by
  apply div_nonneg
  · exact productSectionAverage_nonneg μ T A z _ (fun y => mul_nonneg (hrho y) (hF y)) x
  · exact productSectionAverage_nonneg μ T A z rho hrho x

theorem productSectionDensityWeight_le (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productSectionDensityWeight μ T A z rho F x ≤ M := by
  unfold productSectionDensityWeight
  by_cases hz : productSectionAverage μ T A z rho x = 0
  · rw [hz, div_zero]
    exact hM
  · have hp : 0 < productSectionAverage μ T A z rho x :=
      lt_of_le_of_ne (productSectionAverage_nonneg μ T A z rho hrho x) (Ne.symm hz)
    exact (div_le_iff₀ hp).mpr (productSectionAverage_weighted_cap μ T A z rho F hrho hF x).2

theorem productSectionDensityWeight_mul (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productSectionAverage μ T A z rho x * productSectionDensityWeight μ T A z rho F x =
      productSectionAverage μ T A z (fun y => rho y * F y) x := by
  by_cases hz : productSectionAverage μ T A z rho x = 0
  · rw [hz, zero_mul, productSectionAverage_weighted_zero μ T A z rho F hrho hF x hz]
  · unfold productSectionDensityWeight
    field_simp

theorem productNormalizedSectionWeight_nonneg (T A : Finset I) (z : ∀ i, X i)
    {K : ℝ} (hK : 0 ≤ K) (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x) (x : ∀ i, X i) :
    0 ≤ productNormalizedSectionWeight μ T A z K rho F x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hK _)) (productSectionDensityWeight_nonneg μ T A z rho F hrho hF x)

theorem productNormalizedSectionWeight_le (T A : Finset I) (z : ∀ i, X i)
    {K M : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productNormalizedSectionWeight μ T A z K rho F x ≤ M := by
  have hp : 1 ≤ K ^ A.card := one_le_pow₀ hK
  exact (mul_le_mul_of_nonneg_left (productSectionDensityWeight_le μ T A z rho F hrho hM hF x)
    (inv_nonneg.mpr (zero_le_one.trans hp))).trans
    ((mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hp) hM).trans_eq (one_mul M))

theorem productNormalizedSection_weighted_eq (T A : Finset I) (z : ∀ i, X i) (K : ℝ)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) {M : ℝ}
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (x : ∀ i, X i) :
    productNormalizedSection μ T A z K (fun y => rho y * F y) x =
      productSectionAverage μ T A z rho x * productNormalizedSectionWeight μ T A z K rho F x := by
  unfold productNormalizedSection productNormalizedSectionWeight
  rw [← productSectionDensityWeight_mul μ T A z rho F hrho hF x]
  ring

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

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem exists_massNormalizedSection_density_data
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {m τ η : ℝ} (hτ : 0 < τ) (hm : τ ≤ m) {s : ℕ} (hAs : A.card ≤ s)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hclose : ProductMarginalsClose μ rho η s) :
    ∃ rho' f' : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ rho' x) ∧ (∀ x, 0 ≤ f' x ∧ f' x ≤ τ⁻¹) ∧
      (fun x => m⁻¹ * productSectionAverage μ T A z (fun y => rho y * f y) x) =
        (fun x => rho' x * f' x) ∧
      ProductMarginalsClose μ rho' η (s - A.card) := by
  let rho' := productSectionAverage μ T A z rho
  let f' := fun x => m⁻¹ * productSectionDensityWeight μ T A z rho f x
  have hmpos : 0 < m := hτ.trans_le hm
  have hinv : m⁻¹ ≤ τ⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hτ hm
  refine ⟨rho', f', productSectionAverage_nonneg μ T A z rho hrho, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hmpos.le)
        (productSectionDensityWeight_nonneg μ T A z rho f hrho (fun y => (hf y).1) x)
    · change m⁻¹ * productSectionDensityWeight μ T A z rho f x ≤ τ⁻¹
      calc
        _ ≤ m⁻¹ * 1 := mul_le_mul_of_nonneg_left
          (productSectionDensityWeight_le μ T A z rho f hrho zero_le_one hf x) (inv_nonneg.mpr hmpos.le)
        _ ≤ τ⁻¹ := by simpa only [mul_one] using hinv
  · funext x
    dsimp only [rho', f']
    rw [← productSectionDensityWeight_mul μ T A z rho f hrho hf x]
    ring
  · exact ProductMarginalsClose.section μ hclose T A hAT hAs z hz

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productNormalizedSection_density_data (T A : Finset I) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    {K M eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) {r s : ℕ}
    (hAr : A.card ≤ r) (hAs : A.card ≤ s)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta s)
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    ∃ rho' F' : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ rho' x) ∧ (∀ x, 0 ≤ F' x ∧ F' x ≤ M) ∧
      productNormalizedSection μ T A z K (fun x => rho x * F x) = (fun x => rho' x * F' x) ∧
      ProductMarginalsClose μ rho' eta (s - A.card) ∧
      ProductBoundedMarginals μ (fun x => rho' x * F' x) K (r - A.card) := by
  let rho' := productSectionAverage μ T A z rho
  let F' := productNormalizedSectionWeight μ T A z K rho F
  have he : productNormalizedSection μ T A z K (fun x => rho x * F x) = (fun x => rho' x * F' x) :=
    funext (productNormalizedSection_weighted_eq μ T A z K rho F hrho hF)
  refine ⟨rho', F', productSectionAverage_nonneg μ T A z rho hrho, ?_, he, ?_, ?_⟩
  · intro x
    exact ⟨productNormalizedSectionWeight_nonneg μ T A z (zero_le_one.trans hK) rho F hrho
      (fun y => (hF y).1) x, productNormalizedSectionWeight_le μ T A z hK hM rho F hrho hF x⟩
  · exact ProductMarginalsClose.section μ hclose T A hAT hAs z hz
  · rw [← he]
    exact productNormalizedSection_boundedMarginals μ T A hAT z hz hK hAr _ hbound

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

theorem normalized_density_data (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (c : ProductCylinder X) {τ η : ℝ} (hτ : 0 < τ)
    (hm : τ ≤ c.mass μ base (observedProductDensity μ p F w))
    {s : ℕ} (hcs : c.1.card ≤ s)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η s) :
    ∃ rho' f' : (∀ i, X i) → ℝ,
      (∀ x, 0 ≤ rho' x) ∧ (∀ x, 0 ≤ f' x ∧ f' x ≤ τ⁻¹) ∧
      normalizedSection μ base (observedProductDensity μ p F w) c = (fun x => rho' x * f' x) ∧
      ProductMarginalsClose μ rho' η (s - c.1.card) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w 1 zero_le_one hw
  have hrho := observedProductDensity_nonneg μ p F (fun _ => 1) (fun _ => zero_le_one)
  have hz : (FiniteProbabilityWeights.pi μ).weight (c.assignment base) ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (c.assignment base i))).ne'
  obtain ⟨rho', f', hrho', hf', he', hc⟩ := exists_massNormalizedSection_density_data μ c.1 c.1
    (by rfl) (c.assignment base) hz hτ hm hcs
    (observedProductDensity μ p F (fun _ => 1)) f hrho hf hclose
  refine ⟨rho', f', hrho', hf', ?_, hc⟩
  have hsec := congrArg (productSectionAverage μ c.1 c.1 (c.assignment base)) he
  unfold normalizedSection
  rw [hsec]
  exact he'

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

theorem cut_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.cut F w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_nonneg (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : 0 ≤ c.erase F w z := by
  unfold erase
  split_ifs <;> simp [hw]

theorem cut_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.cut F w z ≤ w z := by
  unfold cut
  split_ifs <;> simp [hw]

theorem erase_le (c : ProductCylinder X) (F : Ω → ∀ i, X i) (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z) (z : Ω) : c.erase F w z ≤ w z := by
  unfold erase
  split_ifs <;> simp [hw]

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

theorem section_cut (x : ∀ i, X i) :
    productSectionAverage μ c.1 c.1 (c.assignment base) (observedProductDensity μ p F (c.cut F w)) x =
      productSectionAverage μ c.1 c.1 (c.assignment base) (observedProductDensity μ p F w) x := by
  unfold productSectionAverage
  congr 1
  funext y
  rw [c.density_cut]
  apply if_pos
  intro i
  simpa only [productCoordinateMix, i.property, ite_true] using c.assignment_mem base i.val i.property

theorem normalizedSection_cut :
    normalizedSection μ base (observedProductDensity μ p F (c.cut F w)) c =
      normalizedSection μ base (observedProductDensity μ p F w) c := by
  funext x
  unfold normalizedSection
  rw [c.mass_cut_self μ base p F w, c.section_cut μ base p F w x]

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

theorem removedCylinderWeights_bounds {Ω ι : Type*} {X : ι → Type*}
    (F : Ω → ∀ i, X i) (w : Ω → ℝ) (cs : List (ProductCylinder X))
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    {f : Ω → ℝ} (hf : f ∈ removedCylinderWeights F w cs) (z : Ω) :
    0 ≤ f z ∧ f z ≤ 1 := by
  induction cs generalizing w with
  | nil => simp only [removedCylinderWeights, List.not_mem_nil] at hf
  | cons c cs ih =>
    change f ∈ c.cut F w :: removedCylinderWeights F (c.erase F w) cs at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨c.cut_nonneg F w hw0 z, (c.cut_le F w hw0 z).trans (hw1 z)⟩
    · exact ih (c.erase F w) (c.erase_nonneg F w hw0)
        (fun x => (c.erase_le F w hw0 x).trans (hw1 x)) hf

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

theorem productSection_truncatedGram_bound (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {M η : ℝ} (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (fun x => rho x * f x)) ≤
      2 * M * (FiniteProbabilityWeights.pi μ).mean
        (productSectionAverage μ T A z (fun x => rho x * f x)) +
      2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc : ProductMarginalsClose μ (productSectionAverage μ T A z rho) η (2 * b) := by
    simpa only [Nat.add_sub_cancel] using
      ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have h := productTruncatedGram_bound μ (productSectionAverage μ T A z rho)
    (productSectionDensityWeight μ T A z rho f)
    (productSectionAverage_nonneg μ T A z rho hrho)
    (fun x => ⟨productSectionDensityWeight_nonneg μ T A z rho f hrho (fun y => (hf y).1) x,
      productSectionDensityWeight_le μ T A z rho f hrho hM hf x⟩) hη D hcard hc
  simpa only [productSectionDensityWeight_mul μ T A z rho f hrho hf] using h

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productSection_truncatedGram_uniform (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (rho f : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x)
    {M η : ℝ} (hM : 0 ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ rho η (2 * b + A.card)) :
    productANOVAEnergy μ D (productSectionAverage μ T A z (fun x => rho x * f x)) ≤
      2 * M ^ 2 * (1 + η) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2 := by
  have hc := ProductMarginalsClose.section μ hclose T A hAT (by omega) z hz
  have hmean := hc ∅ (by simp) z hz
  rw [productConditionalMean_empty] at hmean
  have hmass : (FiniteProbabilityWeights.pi μ).mean
      (productSectionAverage μ T A z (fun x => rho x * f x)) ≤ M * (1 + η) := by
    calc
      _ ≤ (FiniteProbabilityWeights.pi μ).mean (fun x => M * productSectionAverage μ T A z rho x) :=
        (FiniteProbabilityWeights.pi μ).mean_mono
          (fun x => (productSectionAverage_weighted_cap μ T A z rho f hrho hf x).2)
      _ = M * (FiniteProbabilityWeights.pi μ).mean (productSectionAverage μ T A z rho) :=
        (FiniteProbabilityWeights.pi μ).mean_const_mul M _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hmean).2]) hM
  have h := productSection_truncatedGram_bound μ T A hAT z hz rho f hrho hM hf hη D hcard hclose
  nlinarith [mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)]

theorem observedProductDensity_section_norm_uniform {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)
    (T A : Finset ι) (hAT : A ⊆ T)
    (z : ∀ i, X i) (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0)
    (w : Ω → ℝ) {M η : ℝ} (hM : 0 ≤ M)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ M) (hη : 0 ≤ η)
    (D : Finset (Finset ι)) {b : ℕ} (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card)) :
    Real.sqrt (productANOVAEnergy μ D (productSectionAverage μ T A z (observedProductDensity μ p F w))) ≤
      Real.sqrt (2 * M ^ 2 * (1 + η) +
        2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * M ^ 2 * (1 + η) ^ 2) := by
  obtain ⟨f, hf, he⟩ := observedProductDensity_bounded_factor μ p F w M hM hw
  rw [he]
  apply Real.sqrt_le_sqrt
  exact productSection_truncatedGram_uniform μ T A hAT z hz
    (observedProductDensity μ p F (fun _ => 1)) f
    (observedProductDensity_nonneg μ p F (fun _ => 1) (by intro x; norm_num)) hM hf hη D hcard hclose

end Erdos3

end

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

end Erdos3

end

section

namespace Erdos3

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

theorem observedProductDensity_section_norm_le_three (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy μ D
      (productSectionAverage μ T A z (observedProductDensity μ p F w))) ≤ 3 := by
  have h := observedProductDensity_section_norm_uniform μ p F T A hAT z hz w
    zero_le_one hw hη0 D hcard hclose
  simp only [one_pow, mul_one] at h
  apply h.trans
  calc
    _ ≤ Real.sqrt 9 := Real.sqrt_le_sqrt (by linarith)
    _ = 3 := by norm_num

theorem observedProductDensity_scaled_section_norm (w : Ω → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) {scale cap : ℝ}
    (hscale : 0 < scale) (hcap : scale⁻¹ ≤ cap)
    (T A : Finset ι) (hAT : A ⊆ T) (z : ∀ i, X i)
    (hz : (FiniteProbabilityWeights.pi μ).weight z ≠ 0) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (D : Finset (Finset ι)) {b : ℕ}
    (hcard : ∀ S ∈ D, S.card ≤ b)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b + A.card))
    (herr : 2 * η * (D.card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1) :
    Real.sqrt (productANOVAEnergy μ D
      (fun y => scale⁻¹ * productSectionAverage μ T A z (observedProductDensity μ p F w) y)) ≤ 3 * cap := by
  rw [sqrt_productANOVAEnergy_smul, abs_of_nonneg (inv_nonneg.mpr hscale.le)]
  have h := observedProductDensity_section_norm_le_three μ p F w hw T A hAT z hz
    hη0 hη1 D hcard hclose herr
  calc
    _ ≤ scale⁻¹ * 3 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hscale.le)
    _ ≤ 3 * cap := by nlinarith

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAWeightedEnergy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_weighted_energy_le_lp (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (D : Finset (Finset I))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : 1 / p + 1 / q = 1) :
    productANOVAEnergy μ D (fun x => rho x * F x) ≤
      finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) p F *
        finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) q
          (productANOVATruncation μ D (fun x => rho x * F x)) := by
  let P := productANOVATruncation μ D (fun x => rho x * F x)
  rw [productANOVAEnergy_pairing]
  have he : (FiniteProbabilityWeights.pi μ).mean (fun x => (rho x * F x) * P x) =
      ∑ x, ((FiniteProbabilityWeights.pi μ).weight x * rho x) * (F x * P x) := by
    unfold FiniteProbabilityWeights.mean
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  exact (le_abs_self _).trans (finiteWeightedHolder_pair _
    (fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x)) p q hp hq hpq F P)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FiniteMarginalLowDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductBoundedMarginals.mean_le_one {f : (∀ i, X i) → ℝ} {K : ℝ} {r : ℕ}
    (hf : ProductBoundedMarginals μ f K r) : (FiniteProbabilityWeights.pi μ).mean f ≤ 1 := by
  obtain ⟨x, hx⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  simpa only [Finset.card_empty, pow_zero, productConditionalMean_empty] using
    hf ∅ (Nat.zero_le r) x hx

theorem productANOVAEnergy_level_zero (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ (Finset.univ.powersetCard 0) f =
      ((FiniteProbabilityWeights.pi μ).mean f) ^ 2 := by
  rw [Finset.powersetCard_zero]
  simp only [productANOVAEnergy, Finset.sum_singleton, productANOVA_empty,
    FiniteProbabilityWeights.mean_const]

theorem sqrt_productANOVAEnergy_level_zero (f : (∀ i, X i) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard 0) f) =
      (FiniteProbabilityWeights.pi μ).mean f := by
  rw [productANOVAEnergy_level_zero, Real.sqrt_sq ((FiniteProbabilityWeights.pi μ).mean_nonneg hf)]

theorem productANOVAEnergy_level_of_card_lt (k : ℕ) (hk : Fintype.card I < k)
    (f : (∀ i, X i) → ℝ) : productANOVAEnergy μ (Finset.univ.powersetCard k) f = 0 := by
  rw [Finset.powersetCard_eq_empty.mpr (by simpa only [Finset.card_univ] using hk)]
  exact Finset.sum_empty

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_step (k r q : ℕ) (hk : 0 < k) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) (base : ∀ i, X i) (x₀ : Sigma X)
    {K M R eta : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta) (hR : 1 + K ≤ R)
    (hlog : Real.log (2 + M) ≤ (q : ℝ))
    (hcoeff : 2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k ≤ R ^ (2 * k))
    (hbudget : eta * approxMomentEnvelope (Fintype.card I) r M ^ q ≤ 1 / 2)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r)
    (hLower : ∀ T : Finset I, 0 < T.card → T.card ≤ k → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (k - T.card))
          (productNormalizedSection μ T A a K (fun x => rho x * F x))) ≤ R ^ (2 * (k - T.card))) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤ R ^ (2 * k) := by
  let w := fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x
  let P := productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)
  let C := max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)))
    (R ^ (2 * k - 1))
  have hw : ∀ x, 0 ≤ w x := fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x)
  have hq0 : 0 < q := by omega
  have hqr : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqR : 0 < (q : ℝ) := by linarith
  have hp : 0 < (q : ℝ) / ((q : ℝ) - 1) := div_pos hqR (by linarith)
  have hpq : 1 / ((q : ℝ) / ((q : ℝ) - 1)) + 1 / (q : ℝ) = 1 := by field_simp; ring
  have hm : (∑ x, w x * F x) ≤ 1 := by
    simpa only [w, FiniteProbabilityWeights.mean, mul_assoc] using ProductBoundedMarginals.mean_le_one μ hbound
  have hfcap : ∀ x, F x ≤ Real.exp (q : ℝ) := fun x =>
    (hF x).2.trans ((show M ≤ 2 + M by linarith).trans (Real.le_exp_of_log_le hlog))
  have hFnorm := finiteWeighted_conjugate_lp_exp_bound w hw (q : ℝ) hqr F (fun x => (hF x).1) hfcap hm
  have hR1 : 1 ≤ R := by linarith
  have hC1 : 1 ≤ C := (one_le_pow₀ hR1).trans (le_max_right _ _)
  have hC : 0 ≤ C := zero_le_one.trans hC1
  have hn : 1 ≤ ((q * k : ℕ) : ℝ) ^ k := by
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ q * k by nlinarith)
  have hBC : 1 ≤ ((q * k : ℕ) : ℝ) ^ k * C := one_le_mul_of_one_le_of_one_le hn hC1
  have hP := productANOVA_weighted_lp_of_sections μ rho F hrho hM heta hF k q hq0 heven base x₀ C hC
    (ProductMarginalsClose.mono μ hclose (approx_moment_cutoff hkr))
    (approxMomentBudget_error_le_one (Fintype.card I) q hkr hM heta hbudget)
    (productANOVATensor_uniform_of_normalized μ k base hK hR _ hLower)
  have hE : productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x) ≤ R ^ (2 * k) * C := by
    calc
      _ ≤ finiteWeightedLp w ((q : ℝ) / ((q : ℝ) - 1)) F * finiteWeightedLp w (q : ℝ) P :=
        productANOVA_weighted_energy_le_lp μ rho F hrho _ _ _ hp hqR hpq
      _ ≤ Real.exp 1 * finiteWeightedLp w (q : ℝ) P :=
        mul_le_mul_of_nonneg_right hFnorm (finiteWeightedLp_nonneg w hw _ P)
      _ ≤ Real.exp 1 * (((q * k : ℕ) : ℝ) ^ k * C + 1) := mul_le_mul_of_nonneg_left hP (Real.exp_pos 1).le
      _ ≤ Real.exp 1 * (2 * (((q * k : ℕ) : ℝ) ^ k * C)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
      _ = (2 * Real.exp 1 * ((q * k : ℕ) : ℝ) ^ k) * C := by ring
      _ ≤ R ^ (2 * k) * C := mul_le_mul_of_nonneg_right hcoeff hC
  apply anova_bootstrap_le (E := R ^ (2 * k - 1)) (Real.sqrt_nonneg _)
    (pow_nonneg (zero_le_one.trans hR1) _) (pow_le_pow_right₀ hR1 (Nat.sub_le _ _))
  simpa only [Real.sq_sqrt (productANOVAEnergy_nonneg μ _ _)] using hE

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_bound_of_budget (k r q : ℕ) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K M p eta : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p)
    (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hbudget : eta * approxMomentEnvelope (Fintype.card I) r M ^ q ≤ 1 / 2)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
      (8 * (1 + K) * (p + 2)) ^ (2 * k) := by
  classical
  let R := 8 * (1 + K) * (p + 2)
  have hp : 0 ≤ p := (Nat.cast_nonneg r).trans hrp
  have hR : 1 + K ≤ R := by
    dsimp [R]
    nlinarith [mul_nonneg (show 0 ≤ 1 + K by linarith) hp]
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨base, _⟩ := (FiniteProbabilityWeights.pi μ).exists_weight_ne_zero
  have main (n : ℕ) : ∀ s : ℕ, n ≤ s → (s : ℝ) ≤ p →
      eta * approxMomentEnvelope (Fintype.card I) s M ^ q ≤ 1 / 2 →
      ∀ rho F : (∀ i, X i) → ℝ, (∀ x, 0 ≤ rho x) → (∀ x, 0 ≤ F x ∧ F x ≤ M) →
      ProductMarginalsClose μ rho eta (s * (q + 1)) →
      ProductBoundedMarginals μ (fun x => rho x * F x) K s →
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) (fun x => rho x * F x)) ≤ R ^ (2 * n) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hns hsp hbs rho F hrho hF hclose hbound
      by_cases hn : n = 0
      · subst n
        rw [Nat.mul_zero, pow_zero, sqrt_productANOVAEnergy_level_zero μ _ (fun x => mul_nonneg (hrho x) (hF x).1)]
        exact ProductBoundedMarginals.mean_le_one μ hbound
      · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hc : Fintype.card I < n
        · rw [productANOVAEnergy_level_of_card_lt μ n hc, Real.sqrt_zero]
          exact pow_nonneg hR0 _
        · have hncard : n ≤ Fintype.card I := Nat.le_of_not_gt hc
          have hI : Nonempty I := Fintype.card_pos_iff.mp (lt_of_lt_of_le hn0 hncard)
          let i := Classical.choice hI
          apply approxProduct_low_degree_step μ n s q hn0 hns hq heven base ⟨i, base i⟩ hK hM heta hR
            (hlog.trans hpq) (approx_anova_moment_scale hK hp hn0 ((Nat.cast_le.mpr hns).trans hsp) hqp)
            hbs rho F hrho hF hclose hbound
          intro T hT0 hTn z hz A hAT
          have hATc : A.card ≤ T.card := Finset.card_le_card hAT
          have hTs : T.card ≤ s := hTn.trans hns
          have hAs : A.card ≤ s := hATc.trans hTs
          have hAc : A.card ≤ s * (q + 1) := hAs.trans (by nlinarith)
          obtain ⟨rho', F', hrho', hF', he, hc', hb'⟩ :=
            productNormalizedSection_density_data μ T A hAT z hz hK hM hAs hAc rho F hrho hF hclose hbound
          rw [he]
          exact ih (n - T.card) (Nat.sub_lt hn0 hT0) (s - T.card) (Nat.sub_le_sub_right hns T.card)
            ((Nat.cast_le.mpr (Nat.sub_le s T.card)).trans hsp)
            (approxMomentBudget_mono (Fintype.card I) q (Nat.sub_le s T.card) hM heta hbs)
            rho' F' hrho' hF'
            (ProductMarginalsClose.mono μ hc' (approx_section_cutoff (q := q) hATc hTs))
            (ProductBoundedMarginals.mono μ hb' (by omega))
  exact main k r hkr hrp hbudget rho F hrho hF hclose hbound

theorem approxProduct_low_degree_bound (k r q : ℕ) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K M p eta : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hrp : (r : ℝ) ≤ p) (hlog : Real.log (2 + M) ≤ p)
    (hpq : p ≤ (q : ℝ)) (hqp : (q : ℝ) ≤ p + 2)
    (hsmall : eta ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card I : ℝ)) ^ r * (2 + M)) ^ q)⁻¹)
    (rho F : (∀ i, X i) → ℝ) (hrho : ∀ x, 0 ≤ rho x) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M)
    (hclose : ProductMarginalsClose μ rho eta (r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (fun x => rho x * F x) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
      (8 * (1 + K) * (p + 2)) ^ (2 * k) :=
  approxProduct_low_degree_bound_of_budget μ k r q hkr hq heven hK hM heta hrp hlog hpq hqp
    (approxMomentBudget_of_small (Fintype.card I) r q hM hsmall) rho F hrho hF hclose hbound

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

section

namespace Erdos3.ProductCylinder

open scoped BigOperators

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (hμ : ∀ i x, 0 < (μ i).weight x)
  (base : ∀ i, X i) (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

include hμ

theorem normalized_low_degree_bound (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (c : ProductCylinder X) {j k r q : ℕ} (hc : c.1.card ≤ j) (hkr : k ≤ r)
    (hq : 2 ≤ q) (heven : Even q) {K τ η P : ℝ}
    (hK : 1 ≤ K) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hm : τ ≤ c.mass μ base (observedProductDensity μ p F w))
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r * (q + 1)))
    (hbound : ProductBoundedMarginals μ (normalizedSection μ base (observedProductDensity μ p F w) c) K r) :
    Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (normalizedSection μ base (observedProductDensity μ p F w) c)) ≤
        (8 * (1 + K) * (P + 2)) ^ (2 * k) := by
  have hcs : c.1.card ≤ j + r * (q + 1) := by omega
  obtain ⟨rho', f', hrho', hf', he, hc'⟩ := normalized_density_data μ hμ base p F w hw c hτ hm hcs hclose
  have horder : r * (q + 1) ≤ j + r * (q + 1) - c.1.card := by omega
  have hclose' := ProductMarginalsClose.mono μ hc' horder
  have hbound' : ProductBoundedMarginals μ (fun x => rho' x * f' x) K r := by
    rw [← he]
    exact hbound
  rw [he]
  exact approxProduct_low_degree_bound μ k r q hkr hq heven hK (inv_nonneg.mpr hτ.le) hη
    hrP hlog hPq hqP hsmall rho' f' hrho' hf' hclose' hbound'

end Erdos3.ProductCylinder

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

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
  (F : Ω → ∀ i, X i)

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

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [LinearOrder ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
  {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
  {K τ η P : ℝ} {j r q : ℕ} {w v : Ω → ℝ} {cs : List (ProductCylinder X)}

theorem CylinderRemovalChain.low_degree_bounds
    (hchain : CylinderRemovalChain μ base p F K τ j r w v cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hK : 1 ≤ K) (hτ : 0 < τ) (hη : 0 ≤ η)
    (hq : 2 ≤ q) (heven : Even q) (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (j + r * (q + 1)))
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs), ∀ k : ℕ, k ≤ r →
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤
          (8 * (1 + K) * (P + 2)) ^ (2 * k) := by
  revert hw
  induction hchain with
  | nil =>
    intro hw cf hcf
    simp only [removedCylinderWeights, List.zip_nil_left, List.not_mem_nil] at hcf
  | @cons w v cs c hsize hmass hbounded rest ih =>
    intro hw cf hcf k hk
    change cf ∈ (c, c.cut F w) :: cs.zip (removedCylinderWeights F (c.erase F w) cs) at hcf
    rcases List.mem_cons.mp hcf with hcf | hcf
    · subst cf
      rw [c.normalizedSection_cut μ base p F w]
      exact ProductCylinder.normalized_low_degree_bound μ hμ base p F w hw c hsize hk hq heven
        hK hτ hη hrP hlog hPq hqP hsmall hmass.le hclose hbounded
    · exact ih (fun z => ⟨c.erase_nonneg F w (fun x => (hw x).1) z,
        (c.erase_le F w (fun x => (hw x).1) z).trans (hw z).2⟩) cf hcf k hk

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CylinderUniformSections
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem CylinderRemovalChain.uniform_section_bounds {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [LinearOrder ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P : ℝ} {j r q b : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hK : 1 ≤ K) (hτ : 0 < τ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hq : 2 ≤ q) (heven : Even q)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max (j + r * (q + 1)) (2 * b + j)))
    (herr : 2 * η * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤
          (8 * (1 + K) * (P + 2)) ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤ 3 * τ⁻¹ := by
  have hlo := hchain.low_degree_bounds hμ hK hτ hη0 hq heven hrP hlog hPq hqP hsmall
    (ProductMarginalsClose.mono μ hclose (le_max_left _ _)) hw
  intro cf hcf
  refine ⟨hlo cf hcf, ?_⟩
  obtain ⟨hsize, hmass⟩ := hchain.removed_size_mass cf hcf
  have hweight : ∀ z, 0 ≤ cf.2 z ∧ cf.2 z ≤ 1 :=
    removedCylinderWeights_bounds F w cs (fun z => (hw z).1) (fun z => (hw z).2)
      (List.of_mem_zip hcf).2
  have hz : (FiniteProbabilityWeights.pi μ).weight (cf.1.assignment base) ≠ 0 :=
    (Finset.prod_pos (fun i _ => hμ i (cf.1.assignment base i))).ne'
  have hinv : (cf.1.mass μ base (observedProductDensity μ p F cf.2))⁻¹ ≤ τ⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hτ hmass.le
  exact observedProductDensity_scaled_section_norm μ p F cf.2 hweight (hτ.trans hmass) hinv
    cf.1.1 cf.1.1 le_rfl (cf.1.assignment base) hz hη0 hη1 _
    (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS)
    (ProductMarginalsClose.mono μ hclose (by omega)) herr

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.CylinderRemovalChain.uniform_section_bounds.{u_1, u_2, u_3} := @OAI.Erdos3.CylinderRemovalChain.uniform_section_bounds.{u_1, u_2, u_3}
