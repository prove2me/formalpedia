-- Prove2me | solution 1 for OAI.Erdos3.exists_positive_progression_counting_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:18:39.282739+00:00
-- url     : https://prove2.me/submissions/4c12af16-9187-421b-ad59-cb4d4dfb7989

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B139
import Definitions.Def_OAIE3v2B148
import Definitions.Def_OAIE3v2B179
import Theorems.Thm_OAI_Erdos3_exists_positiveGrid_compression_bound_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnchoredReferenceDomination
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_finset_expect {X Z : Type*} [Fintype Z] (p : FiniteProbabilityWeights Z)
    (A : Finset X) (f : Z → X → ℝ) :
    p.mean (fun z => 𝔼 x ∈ A, f z x) = 𝔼 x ∈ A, p.mean (fun z => f z x) := by
  unfold mean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

end FiniteProbabilityWeights
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem prod_mean
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β]
    (F : ι → β → ℝ) :
    (∏ i, mean (F i)) =
      mean (fun y : ι → β => ∏ i, F i (y i)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CountingKernelOuter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem countingFeature_pair (b t r u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b r sigma v) =
      1 + b * (u + v - 2) + (b ^ 2 + t * r) * (u - 1) * (v - 1) := by
  rw [Fintype.expect_eq_sum_div_card]
  norm_num [countingFeature]
  ring

theorem countingFeature_opposite {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b (-t) sigma v) =
      countingKernel b u v := by
  have hc : b ^ 2 + t * (-t) = 2 * b ^ 2 - b := by nlinarith
  rw [countingFeature_pair, hc]
  rfl

theorem countingFeature_same {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (u v : ℝ) :
    (𝔼 sigma : Bool, countingFeature b t sigma u * countingFeature b t sigma v) =
      positiveCountingKernel b u v := by
  have hc : b ^ 2 + t * t = b := by nlinarith
  rw [countingFeature_pair, hc]
  unfold positiveCountingKernel
  ring

theorem countingKernel_one (u v : ℝ) : countingKernel 1 u v = u * v := by
  unfold countingKernel
  ring

theorem countingKernel_quarter (u v : ℝ) :
    countingKernel (1 / 4) u v = 3 / 8 + (3 / 8) * u + (3 / 8) * v - (1 / 8) * u * v := by
  unfold countingKernel
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingFeatureProduct_pair {I X Y : Type*} [Fintype I] [DecidableEq I]
    (b t r : ℝ) (f : I → X → ℝ) (g : I → Y → ℝ) (x : X) (y : Y) :
    (𝔼 sigma : I → Bool, countingFeatureProduct b t f sigma x * countingFeatureProduct b r g sigma y) =
      ∏ i, (𝔼 sigma : Bool, countingFeature b t sigma (f i x) * countingFeature b r sigma (g i y)) := by
  classical
  simp only [countingFeatureProduct, ← Finset.prod_mul_distrib]
  exact (FixedDensity.prod_mean (fun i sigma => countingFeature b t sigma (f i x) *
    countingFeature b r sigma (g i y))).symm

theorem countingFeatureProduct_mean_pair {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] (b t r : ℝ)
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) *
      (𝔼 y, countingFeatureProduct b r g sigma y)) =
      𝔼 x, 𝔼 y, ∏ i, (𝔼 sigma : Bool,
        countingFeature b t sigma (f i x) * countingFeature b r sigma (g i y)) := by
  simp_rw [Finset.expect_mul_expect]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  exact countingFeatureProduct_pair b t r f g x y

theorem countingKernelProductAverage_factorization {I X Y : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] {b t : ℝ} (ht : t ^ 2 = b * (1 - b))
    (f : I → X → ℝ) (g : I → Y → ℝ) :
    countingKernelProductAverage b f g =
      𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) *
        (𝔼 y, countingFeatureProduct b (-t) g sigma y) := by
  simpa only [countingFeature_opposite ht, countingKernelProductAverage] using
    (countingFeatureProduct_mean_pair b t (-t) f g).symm

theorem countingFeatureProduct_square {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b t : ℝ} (ht : t ^ 2 = b * (1 - b)) (f : I → X → ℝ) :
    (𝔼 sigma : I → Bool, (𝔼 x, countingFeatureProduct b t f sigma x) ^ 2) = positiveKernelGram b f := by
  simpa only [pow_two, countingFeature_same ht, positiveKernelGram] using
    countingFeatureProduct_mean_pair b t t f f

theorem positiveKernelGram_nonneg {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : I → X → ℝ) : 0 ≤ positiveKernelGram b f := by
  rw [← countingFeatureProduct_square (Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))) f]
  exact Finset.expect_nonneg (fun _ _ => sq_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingBernoulli_mean {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : ℝ) :
    (countingBernoulli hb hb1).mean (fun sigma => if sigma then u else 1) = 1 - b + b * u := by
  simpa [FiniteProbabilityWeights.mean, countingBernoulli] using add_comm (b * u) (1 - b)

theorem countingBernoulli_product {I : Type*} [Fintype I] [DecidableEq I]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (u : I → ℝ) :
    (FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)).mean
      (fun choice => ∏ i, if choice i then u i else 1) = ∏ i, (1 - b + b * u i) := by
  rw [FiniteProbabilityWeights.mean_pi_product (fun _ : I => countingBernoulli hb hb1)
    (fun i sigma => if sigma then u i else 1)]
  simp only [countingBernoulli_mean]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem countingKernelProductAverage_outer_sq_le {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (f : Z → I → X → ℝ) (g : Z → I → Y → ℝ) :
    (𝔼 z, countingKernelProductAverage b (f z) (g z)) ^ 2 ≤
      (𝔼 z, positiveKernelGram b (f z)) * (𝔼 z, positiveKernelGram b (g z)) := by
  let t := Real.sqrt (b * (1 - b))
  have ht : t ^ 2 = b * (1 - b) := Real.sq_sqrt (mul_nonneg hb (sub_nonneg.mpr hb1))
  have hnt : (-t) ^ 2 = b * (1 - b) := by simpa only [neg_sq] using ht
  let U : Z × (I → Bool) → ℝ := fun q => 𝔼 x, countingFeatureProduct b t (f q.1) q.2 x
  let V : Z × (I → Bool) → ℝ := fun q => 𝔼 y, countingFeatureProduct b (-t) (g q.1) q.2 y
  have hleft : (𝔼 q, U q * V q) = 𝔼 z, countingKernelProductAverage b (f z) (g z) := by
    rw [expect_prod_split]
    simp only [U, V, ← countingKernelProductAverage_factorization ht]
  have hrightU : (𝔼 q, U q ^ 2) = 𝔼 z, positiveKernelGram b (f z) := by
    rw [expect_prod_split]
    simp only [U, countingFeatureProduct_square ht]
  have hrightV : (𝔼 q, V q ^ 2) = 𝔼 z, positiveKernelGram b (g z) := by
    rw [expect_prod_split]
    simp only [V, countingFeatureProduct_square hnt]
  simpa only [hleft, hrightU, hrightV] using
    Finset.expect_mul_sq_le_sq_mul_sq Finset.univ U V

theorem mean_positiveKernelGram_le_of_boolean_products {I X Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Z]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : Z → I → X → ℝ)
    (h : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) ≤ A) :
    (𝔼 z, positiveKernelGram b (f z)) ≤ A := by
  classical
  let p := FiniteProbabilityWeights.pi (fun _ : I => countingBernoulli hb hb1)
  have hpoint (z : Z) (x y : X) : (∏ i, positiveCountingKernel b (f z i x) (f z i y)) =
      p.mean (fun choice => ∏ i, if choice i then f z i x * f z i y else 1) := by
    simpa only [positiveCountingKernel, mul_assoc] using
      (countingBernoulli_product hb hb1 (fun i => f z i x * f z i y)).symm
  calc
    (𝔼 z, positiveKernelGram b (f z)) =
        p.mean (fun choice => 𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) := by
      simp only [positiveKernelGram, hpoint, FiniteProbabilityWeights.mean_finset_expect]
    _ ≤ p.mean (fun _ => A) := p.mean_mono h
    _ = A := p.mean_const A

theorem countingKernelProductAverage_outer_abs_le {I X Y Z : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) (hA : 0 ≤ A)
    (f : Z → I → X → ℝ) (g : Z → I → Y → ℝ)
    (hf : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then f z i x * f z i y else 1) ≤ A)
    (hg : ∀ choice : I → Bool,
      (𝔼 z, 𝔼 x, 𝔼 y, ∏ i, if choice i then g z i x * g z i y else 1) ≤ A) :
    |𝔼 z, countingKernelProductAverage b (f z) (g z)| ≤ A := by
  have hsq := (countingKernelProductAverage_outer_sq_le hb hb1 f g).trans
    (mul_le_mul (mean_positiveKernelGram_le_of_boolean_products hb hb1 f hf)
      (mean_positiveKernelGram_le_of_boolean_products hb hb1 g hg)
      (Finset.expect_nonneg (fun z _ => positiveKernelGram_nonneg hb hb1 (g z))) hA)
  nlinarith [sq_abs (𝔼 z, countingKernelProductAverage b (f z) (g z)),
    abs_nonneg (𝔼 z, countingKernelProductAverage b (f z) (g z))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicComparisonMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem CyclicNiltestUpperComparison.mean_le {s N : ℕ} [NeZero N] {P error : ℝ}
    {f g : ZMod N → ℝ} (h : CyclicNiltestUpperComparison.{0} s N P error f g)
    (hP : 2 ≤ P) : (𝔼 x, f x) ≤ (𝔼 x, g x) + error := by
  let D := RationalTorus.trivialNilmanifold 0
  let T := RationalFilteredNilmanifold.Niltest.const D (fun _ : Unit => 1) 1
  have hT : T.UnitIntervalValued := by intro z; norm_num [T, RationalFilteredNilmanifold.Niltest.const]
  have hTc : T.ComplexityLE P := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ hP
  have htest := h D (Nat.zero_le s) T hT hTc
  have hd : (𝔼 x, (f x - g x)) ≤ error := by
    simpa only [T, RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_const, Complex.one_re, mul_one] using htest
  rw [Finset.expect_sub_distrib] at hd
  linarith

theorem CyclicNiltestUpperComparison.mean_le_const {s N : ℕ} [NeZero N] {P error c : ℝ}
    {f : ZMod N → ℝ} (h : CyclicNiltestUpperComparison.{0} s N P error f (fun _ => c))
    (hP : 2 ≤ P) : (𝔼 x, f x) ≤ c + error := by
  simpa only [Fintype.expect_const] using CyclicNiltestUpperComparison.mean_le h hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

theorem positiveGrid_normalization_bound {g b : ℝ} (hg : 0 ≤ g) (hb : 1 ≤ b)
    (s V W : ℕ) (hWV : W ≤ V) :
    (b * g) ^ V * (b ^ (s + 1)) ^ W ≤ (g * b ^ (s + 2)) ^ V := by
  calc
    _ ≤ (b * g) ^ V * (b ^ (s + 1)) ^ V :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_pow₀ hb) hWV)
        (pow_nonneg (mul_nonneg (by linarith) hg) _)
    _ = _ := by
      rw [← mul_pow]
      congr 1
      rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring

theorem positiveGrid_compression_errors {q L B R T c : ℝ} (V W : ℕ)
    (hq : 1 ≤ q) (hV : (V : ℝ) * q ≤ B) (hWV : W ≤ V)
    (hc : 0 ≤ c) (hcb : c ≤ Real.exp (2 * q))
    (hR : L + 2 * B + 2 ≤ R) (hRT : R ≤ T) :
    c ^ V * Real.exp (-R) + Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T) ≤
      Real.exp (-L) := by
  have hcpow : c ^ V ≤ Real.exp (2 * B) := by
    calc
      _ ≤ (Real.exp (2 * q)) ^ V := pow_le_pow_left₀ hc hcb V
      _ = Real.exp (2 * ((V : ℝ) * q)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hWB : (W : ℝ) ≤ B := by
    have hcast : (W : ℝ) ≤ V := by exact_mod_cast hWV
    have hvq : (V : ℝ) ≤ (V : ℝ) * q := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg V)
    exact hcast.trans (hvq.trans hV)
  have hWexp : (W : ℝ) ≤ Real.exp B := hWB.trans (by linarith [Real.add_one_le_exp B])
  have hfirst : c ^ V * Real.exp (-R) ≤ Real.exp (2 * B - R) := by
    calc
      _ ≤ Real.exp (2 * B) * Real.exp (-R) :=
        mul_le_mul_of_nonneg_right hcpow (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  have hsecond : Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T) ≤
      Real.exp (2 * B - R) := by
    calc
      _ ≤ (Real.exp B * Real.exp B) * Real.exp (-T) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (Real.exp_le_exp.mpr hV) hWexp (Nat.cast_nonneg W) (Real.exp_nonneg B)
      _ = Real.exp (2 * B - T) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ 2 * Real.exp (2 * B - R) := by linarith
    _ ≤ Real.exp 2 * Real.exp (2 * B - R) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (2 + 2 * B - R) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem exists_positiveGrid_base_budget {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 2 ≤ p → Real.exp (-((p + 2) ^ C)) ≤ epsilon := by
  obtain ⟨a, ha⟩ := exists_nat_ge (-Real.log epsilon)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (Polynomial.C a)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have haP : (a : ℝ) ≤ (p + 2) ^ C := by simpa using hbudget p (by linarith)
  calc
    _ ≤ Real.exp (-(a : ℝ)) := Real.exp_le_exp.mpr (neg_le_neg haP)
    _ ≤ Real.exp (Real.log epsilon) := Real.exp_le_exp.mpr (by linarith)
    _ = epsilon := Real.exp_log hepsilon

end Erdos3

end

section

namespace Erdos3

open Filter Topology

theorem exists_positiveGrid_slack (s : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
      (1 + epsilon) ^ (s + 2) ≤ 1 + delta / 2 := by
  have hcontinuous : ContinuousAt (fun x : ℝ => (1 + x) ^ (s + 2)) 0 := by fun_prop
  have htend : Tendsto (fun x : ℝ => (1 + x) ^ (s + 2)) (𝓝 0) (𝓝 1) := by
    simpa using hcontinuous.tendsto
  have heventually : ∀ᶠ x : ℝ in 𝓝 0, (1 + x) ^ (s + 2) < 1 + delta / 2 :=
    htend.eventually_lt_const (by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp heventually
  let epsilon := min r 1 / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hepsilon1 : epsilon < 1 := by
    dsimp [epsilon]
    have h := min_le_right r (1 : ℝ)
    linarith
  have hepsilonr : epsilon < r := by
    dsimp [epsilon]
    have h := min_le_left r (1 : ℝ)
    linarith
  refine ⟨epsilon, hepsilon, hepsilon1, le_of_lt (hball epsilon ?_)⟩
  simpa [Real.dist_eq, abs_of_pos hepsilon] using hepsilonr

theorem positiveGrid_power_gap {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {V : ℕ} (hV : 1 ≤ V) : a ^ V + (b - a) ≤ b ^ V := by
  cases V with
  | zero => omega
  | succ n =>
    rw [pow_succ, pow_succ]
    have hgap : b - a ≤ a ^ n * (b - a) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ ha) (sub_nonneg.mpr hab)
    calc
      _ ≤ a ^ n * a + a ^ n * (b - a) := add_le_add le_rfl hgap
      _ = a ^ n * b := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hab n) (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positiveGridVolume_succ {j : ℕ} (a : Fin (j + 1) → ℕ) :
    positiveGridVolume a = a 0 * positiveGridVolume (fun i => a i.succ) := by
  exact Fin.prod_univ_succ a

theorem positiveGridVolume_pos {j : ℕ} (a : Fin j → ℕ) (ha : ∀ i, 0 < a i) :
    0 < positiveGridVolume a := Finset.prod_pos (fun i _ => ha i)

theorem positiveGridVolume_le {j : ℕ} (a : Fin j → ℕ) {p : ℝ}
    (ha : ∀ i, (a i : ℝ) ≤ p) : (positiveGridVolume a : ℝ) ≤ p ^ j := by
  calc
    _ = ∏ i, (a i : ℝ) := by simp [positiveGridVolume]
    _ ≤ ∏ _i : Fin j, p := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => ha i)
    _ = _ := by simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem prod_dependent_fin_cons {j : ℕ} {X : Fin (j + 1) → Type*} [∀ i, Fintype (X i)]
    {M : Type*} [CommMonoid M] (F : (∀ i, X i) → M) :
    (∏ x, F x) = ∏ y : ∀ i : Fin j, X i.succ, ∏ a : X 0, F (Fin.cons a y) := by
  calc
    _ = ∏ p : X 0 × (∀ i : Fin j, X i.succ), F (Fin.cons p.1 p.2) := by
      apply Fintype.prod_equiv (Fin.consEquiv X).symm
      intro x
      congr 1
      simp
    _ = _ := by rw [Fintype.prod_prod_type, Finset.prod_comm]

theorem positiveGridMean_first_axis {j : ℕ} (a : Fin (j + 1) → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) :
    positiveGridMean a f = 𝔼 t : Fin (a 0) → G,
      𝔼 u : PositiveGridShifts (fun i => a i.succ) G,
        positiveGridProduct a f (Fin.cons t u) := by
  exact expect_dependent_fin_cons (fun t => positiveGridProduct a f t)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rootGrid_product {R : Type*} [AddCommMonoid R] (r q l : ℕ)
    (F : Fin r → (Fin l → Fin q) → R → ℝ) (root : Fin r → R) (z : Fin l → Fin q → R) :
    positiveGridProduct (Fin.cons r (fun _ : Fin l => q))
      (fun beta => F (beta 0) (fun i => beta i.succ)) (Fin.cons root z) =
      ∏ beta : Fin l → Fin q, ∏ j : Fin r, F j beta (root j + ∑ a, z a (beta a)) := by
  simp only [positiveGridProduct, prod_dependent_fin_cons, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rfl

theorem rootGrid_mean {R : Type*} [AddCommMonoid R] [Fintype R] (r q l : ℕ)
    (F : Fin r → (Fin l → Fin q) → R → ℝ) :
    positiveGridMean (Fin.cons r (fun _ : Fin l => q))
      (fun beta => F (beta 0) (fun i => beta i.succ)) =
      𝔼 z : Fin l → Fin q → R, 𝔼 root : Fin r → R,
        ∏ beta : Fin l → Fin q, ∏ j : Fin r, F j beta (root j + ∑ a, z a (beta a)) := by
  rw [positiveGridMean_first_axis, Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro z _
  apply Finset.expect_congr rfl
  intro root _
  exact rootGrid_product r q l F root z

theorem scaledRootGrid_mean {R : Type*} [CommRing R] [Fintype R] (r q l : ℕ)
    (coeff : Fin l → R) (hcoeff : ∀ i, IsUnit (coeff i))
    (F : Fin r → (Fin l → Fin q) → R → ℝ) :
    (𝔼 z : Fin l → Fin q → R, 𝔼 root : Fin r → R,
      ∏ beta : Fin l → Fin q, ∏ j : Fin r, F j beta (root j + ∑ a, coeff a * z a (beta a))) =
      positiveGridMean (Fin.cons r (fun _ : Fin l => q))
        (fun beta => F (beta 0) (fun i => beta i.succ)) := by
  classical
  choose u hu using hcoeff
  let e : (Fin l → Fin q → R) ≃ (Fin l → Fin q → R) :=
    Equiv.piCongrRight (fun a => Equiv.piCongrRight (fun _ : Fin q => (u a).mulLeft))
  have he (z : Fin l → Fin q → R) (a : Fin l) (b : Fin q) : e z a b = coeff a * z a b := by
    change (u a : R) * z a b = coeff a * z a b
    rw [hu]
  rw [rootGrid_mean]
  apply Fintype.expect_equiv e
  intro z
  simp only [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positiveGridProduct_one_axis (a : Fin 1 → ℕ) {G : Type*} [AddCommMonoid G]
    (f : PositiveGridVertex a → G → ℝ) (t : PositiveGridShifts a G) :
    positiveGridProduct a f t =
      ∏ i : Fin (a 0), f (Fin.cons i (fun j => Fin.elim0 j)) (t 0 i) := by
  unfold positiveGridProduct
  rw [prod_dependent_fin_cons, Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.sum_univ_zero, add_zero]

theorem positiveGridMean_one_axis (a : Fin 1 → ℕ) {G : Type*}
    [AddCommMonoid G] [Fintype G] (f : PositiveGridVertex a → G → ℝ) :
    positiveGridMean a f =
      ∏ i : Fin (a 0), (𝔼 x, f (Fin.cons i (fun j => Fin.elim0 j)) x) := by
  rw [positiveGridMean_first_axis]
  simp only [positiveGridProduct_one_axis, Fin.cons_zero, Fintype.expect_const]
  exact (FixedDensity.prod_mean (fun i x => f (Fin.cons i (fun j => Fin.elim0 j)) x)).symm

theorem positiveGridMean_one_axis_le (a : Fin 1 → ℕ) {N s : ℕ} [NeZero N]
    {P error g : ℝ} (hP : 2 ≤ P) (f : PositiveGridVertex a → ZMod N → ℝ)
    (hf : ∀ b x, 0 ≤ f b x)
    (hcompare : ∀ b, CyclicNiltestUpperComparison.{0} s N P error (f b) (fun _ => g)) :
    positiveGridMean a f ≤ (g + error) ^ positiveGridVolume a := by
  rw [positiveGridMean_one_axis]
  calc
    _ ≤ ∏ _i : Fin (a 0), (g + error) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Finset.expect_nonneg (fun x _ => hf _ x)
      · intro i _
        exact CyclicNiltestUpperComparison.mean_le_const (hcompare _) hP
    _ = _ := by simp [positiveGridVolume]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positiveGridMean_one_axis_slack (a : Fin 1 → ℕ) {N s : ℕ} [NeZero N]
    {P error epsilon g : ℝ} (hP : 2 ≤ P) (hepsilon : 0 ≤ epsilon) (hg : 1 ≤ g)
    (herror0 : 0 ≤ error) (herror : error ≤ epsilon) (f : PositiveGridVertex a → ZMod N → ℝ)
    (hf : ∀ b x, 0 ≤ f b x)
    (hcompare : ∀ b, CyclicNiltestUpperComparison.{0} s N P error (f b) (fun _ => g)) :
    positiveGridMean a f ≤ (g * (1 + epsilon)) ^ positiveGridVolume a := by
  have hmean := positiveGridMean_one_axis_le a hP f hf hcompare
  apply hmean.trans
  apply pow_le_pow_left₀ (by linarith : 0 ≤ g + error)
  nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hg)]

theorem exists_positiveGridEstimate_zero {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ PositiveGridEstimate 0 epsilon C := by
  obtain ⟨C, hC, hbase⟩ := exists_positiveGrid_base_budget hepsilon
  refine ⟨C, hC, ?_⟩
  intro N j _ p L g hp hL hg _ _ _ hj hj1 a _ f hf hcompare
  have hjeq : j = 1 := by omega
  subst j
  have hP : 2 ≤ (p + L + 2) ^ C :=
    (by linarith : 2 ≤ p + L).trans (le_power_budget (by linarith) (by omega))
  have h := positiveGridMean_one_axis_slack a hP hepsilon.le hg (Real.exp_nonneg _) (hbase (by linarith)) f
    (fun b x => (hf b x).1) hcompare
  simpa only [zero_add, pow_one] using h.trans (le_add_of_nonneg_right (Real.exp_nonneg (-L)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGridEstimate_step (s cPrevious : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hprevious : PositiveGridEstimate s epsilon cPrevious) :
    ∃ C : ℕ, 2 ≤ C ∧ PositiveGridEstimate (s + 1) epsilon C := by
  obtain ⟨cBase, _, hsmall⟩ := exists_positiveGrid_base_budget hepsilon
  obtain ⟨cCompression, _, hcompression⟩ :=
    exists_positiveGrid_compression_bound_s2 (s + 1) (by omega) hepsilon hepsilon1
  let X : Polynomial ℕ := Polynomial.X
  let RP := X + 4 * X ^ (s + 3) + 4
  let QP := (X ^ 2 + RP + 2) ^ cPrevious
  let TP := QP + RP
  let PP := (X + TP + 2) ^ cCompression
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget (PP + QP + (X + 2) ^ cBase + 2)
  refine ⟨C, hC, ?_⟩
  intro N j _ p L g hp hL hg hgb hodd hN hjpos hj a ha f hf hcompare
  let q := p + L
  let B := q ^ (s + 3)
  let R := q + 4 * B + 4
  let Q := (q ^ 2 + R + 2) ^ cPrevious
  let T := Q + R
  let P := (q + T + 2) ^ cCompression
  have hq : 2 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hLq : L ≤ q := by dsimp [q]; linarith
  have hB : 0 ≤ B := pow_nonneg hq0 _
  have hR : 2 ≤ R := by dsimp [R]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hT : 2 ≤ T := by dsimp [T]; linarith
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hcBase : 0 ≤ (q + 2) ^ cBase := pow_nonneg (by linarith) _
  have hcost : P + Q + (q + 2) ^ cBase + 2 ≤ (q + 2) ^ C := by
    simpa [X, RP, QP, TP, PP, P, T, Q, R, B, Polynomial.eval₂_pow] using hbudget q hq0
  have hcostP : P ≤ (q + 2) ^ C := by linarith
  have hcostQ : Q ≤ (q + 2) ^ C := by linarith
  have hcostBase : (q + 2) ^ cBase ≤ (q + 2) ^ C := by linarith
  have hQT : Q ≤ T := by dsimp [T]; linarith
  have hRT : R ≤ T := by dsimp [T]; linarith
  have hinput : 2 ≤ (q + 2) ^ C := hq.trans (le_power_budget hq0 (by omega))
  have hsmallC : Real.exp (-((q + 2) ^ C)) ≤ epsilon :=
    (Real.exp_le_exp.mpr (neg_le_neg hcostBase)).trans (hsmall hq)
  have hg0 : 0 ≤ g := by linarith
  have hb : 1 ≤ 1 + epsilon := by linarith
  have hb0 : 0 ≤ 1 + epsilon := by linarith
  by_cases hjone : j = 1
  · subst j
    have hmean := positiveGridMean_one_axis_slack a hinput hepsilon.le hg
      (Real.exp_nonneg _) hsmallC f (fun b x => (hf b x).1) hcompare
    have hbase : g * (1 + epsilon) ≤ g * (1 + epsilon) ^ (s + 2) := by
      apply mul_le_mul_of_nonneg_left _ hg0
      simpa only [pow_one] using pow_le_pow_right₀ hb (show 1 ≤ s + 2 by omega)
    calc
      _ ≤ (g * (1 + epsilon)) ^ positiveGridVolume a := hmean
      _ ≤ (g * (1 + epsilon) ^ (s + 2)) ^ positiveGridVolume a :=
        pow_le_pow_left₀ (mul_nonneg hg0 hb0) hbase _
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_nonneg (-L))
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    let V := positiveGridVolume a
    let W := positiveGridVolume (fun i => a i.succ)
    let c := (1 + epsilon) * g
    let A := ((1 + epsilon) ^ (s + 1)) ^ W + Real.exp (-R)
    have hA : 0 ≤ A := add_nonneg (pow_nonneg (pow_nonneg hb0 _) _) (Real.exp_nonneg _)
    have hqSquare : q ≤ q ^ 2 := by nlinarith
    have hqSquare2 : 2 ≤ q ^ 2 := hq.trans hqSquare
    have htail : ∀ h : PositiveGridVertex (fun i => a i.succ) → ZMod N → ℝ,
        (∀ b x, 0 ≤ h b x ∧ h b x ≤ Real.exp (q ^ 2)) →
        (∀ b, CyclicNiltestUpperComparison.{0} ((s + 1) - 1) N T (Real.exp (-T)) (h b) (fun _ => 1)) →
        positiveGridMean (fun i => a i.succ) h ≤ A := by
      intro h hcap htest
      have hh := hprevious hqSquare2 hR (le_refl (1 : ℝ))
        (Real.one_le_exp (by positivity : 0 ≤ q ^ 2)) hodd
        ((Real.exp_le_exp.mpr hcostQ).trans hN) (show 1 ≤ k + 1 by omega)
        (show k + 1 ≤ s + 1 by omega) (fun i => a i.succ)
        (fun i => ⟨(ha i.succ).1, (ha i.succ).2.trans (hpq.trans hqSquare)⟩) h hcap
        (fun b => CyclicNiltestUpperComparison.mono_budget (htest b) hQT
          (Real.exp_le_exp.mpr (neg_le_neg hQT)))
      simpa only [one_mul] using hh
    have hgrid := hcompression hq hT hg (hgb.trans (Real.exp_le_exp.mpr hpq)) hA hodd
      ((Real.exp_le_exp.mpr hcostP).trans hN) a ((ha 0).2.trans hpq) f
      (fun b x => ⟨(hf b x).1, (hf b x).2.trans (Real.exp_le_exp.mpr hpq)⟩)
      (fun b => CyclicNiltestUpperComparison.mono_budget (hcompare b) hcostP
        (Real.exp_le_exp.mpr (neg_le_neg hcostP))) htail
    have hWV : W ≤ V := by
      calc
        W = 1 * W := by omega
        _ ≤ a 0 * W := Nat.mul_le_mul_right W (ha 0).1
        _ = V := (positiveGridVolume_succ a).symm
    have hV : (V : ℝ) * q ≤ B := by
      have hvolume : (V : ℝ) ≤ q ^ (s + 2) :=
        (positiveGridVolume_le a (fun i => (ha i).2.trans hpq)).trans
          (pow_le_pow_right₀ hq1 hj)
      calc
        _ ≤ q ^ (s + 2) * q := mul_le_mul_of_nonneg_right hvolume hq0
        _ = B := (pow_succ q (s + 2)).symm
    have hc0 : 0 ≤ c := mul_nonneg hb0 hg0
    have hcb : c ≤ Real.exp (2 * q) := by
      calc
        c ≤ 2 * Real.exp q := mul_le_mul (by linarith) (hgb.trans (Real.exp_le_exp.mpr hpq)) hg0 (by norm_num)
        _ ≤ Real.exp q * Real.exp q :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp q]) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have herr := positiveGrid_compression_errors V W hq1 hV hWV hc0 hcb
      (show L + 2 * B + 2 ≤ R by dsimp [R]; linarith) hRT
    have hmain := positiveGrid_normalization_bound hg0 hb s V W hWV
    calc
      positiveGridMean a f ≤ c ^ V * A + Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T) := hgrid
      _ = c ^ V * ((1 + epsilon) ^ (s + 1)) ^ W +
          (c ^ V * Real.exp (-R) + Real.exp ((V : ℝ) * q) * (W : ℝ) * Real.exp (-T)) := by
        dsimp [A]
        ring
      _ ≤ (g * (1 + epsilon) ^ (s + 2)) ^ V + Real.exp (-L) := add_le_add hmain herr

theorem exists_positiveGridEstimate (s : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ PositiveGridEstimate s epsilon C := by
  induction s with
  | zero => exact exists_positiveGridEstimate_zero hepsilon
  | succ s ih =>
    obtain ⟨cPrevious, _, hprevious⟩ := ih
    exact exists_positiveGridEstimate_step s cPrevious hepsilon hepsilon1 hprevious

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positiveGrid_counting (s : ℕ) {delta C0 : ℝ}
    (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧ ∀ {N j : ℕ} [NeZero N] {p xi : ℝ},
      2 ≤ p → 0 < xi → xi ≤ xi0 → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      1 ≤ j → j ≤ s + 1 → ∀ a : Fin j → ℕ,
      (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ C0 * p) →
      ∀ f : PositiveGridVertex a → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (f b) (fun _ => 1 + xi)) →
      positiveGridMean a f ≤ (1 + delta) ^ positiveGridVolume a := by
  obtain ⟨epsilon, hepsilon, hepsilon1, hslack⟩ := exists_positiveGrid_slack s hdelta
  obtain ⟨c, _, hgrid⟩ := exists_positiveGridEstimate s hepsilon hepsilon1
  obtain ⟨A, hA⟩ := exists_nat_ge C0
  obtain ⟨ell, hell⟩ := exists_nat_ge (max 2 (-Real.log (delta / 2)))
  have hell2 : (2 : ℝ) ≤ ell := (le_max_left _ _).trans hell
  have hlog : -Real.log (delta / 2) ≤ ell := (le_max_right _ _).trans hell
  have herror : Real.exp (-(ell : ℝ)) ≤ delta / 2 := by
    calc
      _ ≤ Real.exp (Real.log (delta / 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log (by linarith)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.C A * (X + 1) + Polynomial.C ell + 2) ^ c)
  refine ⟨C, hC, epsilon, hepsilon, ?_⟩
  intro N j _ p xi hp hxi hxiepsilon hodd hN hj hjbound a ha f hf hcompare
  let q : ℝ := A * (p + 1)
  have hA1 : (1 : ℝ) ≤ A := hC0.trans hA
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hp0 : 0 ≤ p := by linarith
  have hpq : p ≤ q := by
    dsimp [q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hA1) (show 0 ≤ p + 1 by linarith)]
  have hq : 2 ≤ q := hp.trans hpq
  have hcost : (q + ell + 2) ^ c ≤ (p + 2) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp0
  have hgb : 1 + xi ≤ Real.exp q := by
    have h := Real.add_one_le_exp q
    linarith
  have hbound (i) : (a i : ℝ) ≤ q := by
    calc
      _ ≤ C0 * p := (ha i).2
      _ ≤ (A : ℝ) * p := mul_le_mul_of_nonneg_right hA hp0
      _ ≤ q := mul_le_mul_of_nonneg_left (by linarith : p ≤ p + 1) hA0
  have h := hgrid hq hell2 (by linarith : 1 ≤ 1 + xi) hgb hodd
    ((Real.exp_le_exp.mpr hcost).trans hN) hj hjbound a
    (fun i => ⟨(ha i).1, hbound i⟩) f
    (fun b x => ⟨(hf b x).1, (hf b x).2.trans (Real.exp_le_exp.mpr hpq)⟩)
    (fun b => CyclicNiltestUpperComparison.mono_budget (hcompare b) hcost
      (Real.exp_le_exp.mpr (neg_le_neg hcost)))
  have hb0 : 0 ≤ 1 + epsilon := by linarith
  have hmain : (1 + xi) * (1 + epsilon) ^ (s + 1) ≤ 1 + delta / 2 := by
    calc
      _ ≤ (1 + epsilon) * (1 + epsilon) ^ (s + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hb0 _)
      _ = (1 + epsilon) ^ (s + 2) := (pow_succ' _ _).symm
      _ ≤ _ := hslack
  have hvolume : 1 ≤ positiveGridVolume a :=
    positiveGridVolume_pos a (fun i => (ha i).1)
  have hgap := positiveGrid_power_gap (by linarith : 1 ≤ 1 + delta / 2)
    (by linarith : 1 + delta / 2 ≤ 1 + delta) hvolume
  calc
    _ ≤ ((1 + xi) * (1 + epsilon) ^ (s + 1)) ^ positiveGridVolume a + Real.exp (-(ell : ℝ)) := h
    _ ≤ (1 + delta / 2) ^ positiveGridVolume a + delta / 2 :=
      add_le_add (pow_le_pow_left₀ (mul_nonneg (by linarith) (pow_nonneg hb0 _)) hmain _) herror
    _ ≤ _ := by convert hgap using 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem CyclicNiltestUpperComparison.of_pointwise.{universeLevel} {s N : ℕ} [NeZero N]
    {P error : ℝ} {f g : ZMod N → ℝ} (hfg : ∀ x, f x ≤ g x) (herror : 0 ≤ error) :
    CyclicNiltestUpperComparison.{universeLevel} s N P error f g := by
  intro L _ _ degree dim _ _ _ _ D _ T hT _
  apply le_trans _ herror
  refine (Finset.expect_le_expect (fun x _ => ?_)).trans_eq (Fintype.expect_const (0 : ℝ))
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hfg x))
    (T.unit_interval_evalCyclic hT N (fun _ => x)).2.1

theorem exists_positiveGrid_family_counting (s : ℕ) {delta C0 : ℝ}
    (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {I : Type*} {N j : ℕ} [NeZero N] {p xi : ℝ},
      2 ≤ p → 0 < xi → xi ≤ xi0 → Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      1 ≤ j → j ≤ s + 1 → ∀ a : Fin j → ℕ,
      (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ C0 * p) → ∀ f : I → ZMod N → ℝ,
      (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
      (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (f b) (fun _ => 1 + xi)) →
      ∀ choice : PositiveGridVertex a → Option I,
      positiveGridMean a (fun b x => (choice b).elim 1 (fun i => f i x)) ≤
        (1 + delta) ^ positiveGridVolume a := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_positiveGrid_counting s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro I N j _ p xi hp hxi hxib hodd hN hj hjb a ha f hf hcompare choice
  apply hgrid hp hxi hxib hodd hN hj hjb a ha
  · intro b x
    cases hc : choice b with
    | none => simpa only [hc, Option.elim_none] using
        (show (0 : ℝ) ≤ 1 ∧ 1 ≤ Real.exp p from ⟨zero_le_one, Real.one_le_exp (by linarith)⟩)
    | some i => simpa only [hc, Option.elim_some] using hf i x
  · intro b
    cases hc : choice b with
    | none =>
      change CyclicNiltestUpperComparison s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (fun _ => 1) (fun _ => 1 + xi)
      exact CyclicNiltestUpperComparison.of_pointwise (fun _ => by linarith) (Real.exp_nonneg _)
    | some i =>
      change CyclicNiltestUpperComparison s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (f i) (fun _ => 1 + xi)
      exact @hcompare i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotStageBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_independent_product {G : Type*} [Fintype G] [Nonempty G]
    (q : ℕ) (f : G → ℝ) :
    (𝔼 t : Fin q → G, ∏ i, f (t i)) = (𝔼 x, f x) ^ q := by
  simpa [FixedDensity.mean] using (FixedDensity.prod_mean (fun _i : Fin q => f)).symm

theorem expect_common_shift_product {G : Type*} [AddGroup G] [Fintype G]
    (q : ℕ) (d : G) (f : G → ℝ) :
    (𝔼 t : Fin q → G, ∏ i, f (d + t i)) = (𝔼 x, f x) ^ q := by
  rw [expect_independent_product q (fun x => f (d + x))]
  congr 1
  apply Fintype.expect_equiv (Equiv.addLeft d)
  intro x
  rfl

theorem expect_pivot_change {R : Type*} [Ring R] [Fintype R]
    (p : R) (F : R → R → ℝ) :
    (𝔼 x, 𝔼 d, F x d) = 𝔼 w, 𝔼 d, F (w - p * d) d := by
  rw [Finset.expect_comm, Finset.expect_comm (Finset.univ : Finset R) (Finset.univ : Finset R)
    (fun w d => F (w - p * d) d)]
  apply Finset.expect_congr rfl
  intro d _
  symm
  apply Fintype.expect_equiv (Equiv.addRight (-(p * d)))
  intro w
  change F (w - p * d) d = F (w + -(p * d)) d
  rw [sub_eq_add_neg]

theorem pivot_even_moment {R : Type*} [CommRing R] [Fintype R]
    (q : ℕ) (hq : Even q) (p : R) (H : R → R → ℝ) :
    (𝔼 x, 𝔼 d, 𝔼 t : Fin q → R, ∏ i, H (x - p * t i) (d + t i)) =
      𝔼 w, |𝔼 d, H (w - p * d) d| ^ q := by
  rw [expect_pivot_change p]
  apply Finset.expect_congr rfl
  intro w _
  have hpoint (d : R) :
      (𝔼 t : Fin q → R, ∏ i, H ((w - p * d) - p * t i) (d + t i)) =
        (𝔼 a, H (w - p * a) a) ^ q := by
    have heq (t : Fin q → R) (i : Fin q) :
        H ((w - p * d) - p * t i) (d + t i) = H (w - p * (d + t i)) (d + t i) := by
      congr 1
      ring
    simp_rw [heq]
    exact expect_common_shift_product q d (fun a => H (w - p * a) a)
  simp only [hpoint, Fintype.expect_const, hq.pow_abs]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem twoSlopeMap_bijective {R : Type*} [CommRing R] (a b : R) (hab : IsUnit (b - a)) :
    Function.Bijective (fun z : R × R => (z.1 + a * z.2, z.1 + b * z.2)) := by
  obtain ⟨u, hu⟩ := hab
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    have hd : (u : R) * x.2 = (u : R) * y.2 := by
      rw [hu]
      dsimp at h1 h2
      linear_combination h2 - h1
    have hxy : x.2 = y.2 := u.isUnit.mul_left_cancel hd
    apply Prod.ext
    · dsimp at h1
      rw [hxy] at h1
      exact add_right_cancel h1
    · exact hxy
  · rintro ⟨y, z⟩
    let d := (↑(u⁻¹) : R) * (z - y)
    refine ⟨(y - a * d, d), ?_⟩
    apply Prod.ext
    · dsimp
      ring
    · change y - a * d + b * d = z
      have hd : (b - a) * d = z - y := by
        rw [← hu]
        dsimp [d]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      linear_combination hd

theorem expect_two_slopes {R : Type*} [CommRing R] [Fintype R]
    (a b : R) (hab : IsUnit (b - a)) (F : R → R → ℝ) :
    (𝔼 x, 𝔼 d, F (x + a * d) (x + b * d)) = 𝔼 y, 𝔼 z, F y z := by
  let e := Equiv.ofBijective _ (twoSlopeMap_bijective a b hab)
  have h : (𝔼 q : R × R, F (q.1 + a * q.2) (q.1 + b * q.2)) =
      𝔼 q : R × R, F q.1 q.2 := by
    apply Fintype.expect_equiv e
    intro q
    rfl
  simpa only [expect_prod_split] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem FiniteProbabilityWeights.mean_pow_two_pow_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (n : ℕ) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    p.mean f ^ (2 ^ n) ≤ p.mean (fun x => f x ^ (2 ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (p.mean f ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ (p.mean (fun x => f x ^ (2 ^ n))) ^ 2 :=
        pow_le_pow_left₀ (pow_nonneg (p.mean_nonneg hf) _) ih 2
      _ ≤ p.mean (fun x => (f x ^ (2 ^ n)) ^ 2) := p.mean_square_le _
      _ = _ := by simp only [pow_succ, pow_mul]

theorem weighted_dyadic_holder {X : Type*} [Fintype X] [Nonempty X]
    (n : ℕ) (D F : X → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hD : ∀ x, 0 ≤ D x) (hcap : ∀ x, D x ≤ B) :
    |𝔼 x, D x * F x| ^ (2 ^ n) ≤
      (𝔼 x, D x) ^ (2 ^ n - 1) * B * (𝔼 x, |F x| ^ (2 ^ n)) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hmean : 0 ≤ 𝔼 x, D x := Finset.expect_nonneg (fun x _ => hD x)
  by_cases hm : (𝔼 x, D x) = 0
  · have hsum : ∑ x, D x = 0 := by
      have h := Fintype.card_mul_expect D
      rw [hm, mul_zero] at h
      exact h.symm
    have hzero : ∀ x, D x = 0 := by
      intro x
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hD y)).mp hsum x (Finset.mem_univ x)
    simp only [hzero, zero_mul, Fintype.expect_const, abs_zero, zero_pow hq0]
    positivity
  · have hmpos : 0 < 𝔼 x, D x := lt_of_le_of_ne hmean (Ne.symm hm)
    let p := FiniteProbabilityWeights.uniform X
    have hpm : 0 < p.mean D := by simpa only [p, FiniteProbabilityWeights.uniform_mean] using hmpos
    let w := p.reweightPositive D hD hpm
    have hnorm := w.mean_pow_two_pow_le n (fun x => |F x|) (fun x => abs_nonneg _)
    have hnorm' : ((𝔼 x, D x * |F x|) / (𝔼 x, D x)) ^ (2 ^ n) ≤
        (𝔼 x, D x * |F x| ^ (2 ^ n)) / (𝔼 x, D x) := by
      simpa only [w, FiniteProbabilityWeights.reweightPositive_mean, p,
        FiniteProbabilityWeights.uniform_mean] using hnorm
    rw [div_pow] at hnorm'
    have hweighted := (div_le_iff₀ (pow_pos hmpos (2 ^ n))).mp hnorm'
    have hfactor : (𝔼 x, D x) ^ (2 ^ n) = (𝔼 x, D x) ^ (2 ^ n - 1) * (𝔼 x, D x) := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    have hpoint (x : X) : |D x * F x| = D x * |F x| := by rw [abs_mul, abs_of_nonneg (hD x)]
    have habs : |𝔼 x, D x * F x| ≤ 𝔼 x, D x * |F x| := by
      simpa only [Real.norm_eq_abs, hpoint] using
        (RCLike.norm_expect_le (K := ℝ) (f := fun x => D x * F x))
    have hmoment : (𝔼 x, D x * |F x| ^ (2 ^ n)) ≤ B * (𝔼 x, |F x| ^ (2 ^ n)) := by
      calc
        _ ≤ 𝔼 x, B * |F x| ^ (2 ^ n) :=
          Finset.expect_le_expect (fun x _ => mul_le_mul_of_nonneg_right (hcap x) (pow_nonneg (abs_nonneg _) _))
        _ = _ := (Finset.mul_expect _ _ _).symm
    calc
      _ ≤ (𝔼 x, D x * |F x|) ^ (2 ^ n) := pow_le_pow_left₀ (abs_nonneg _) habs _
      _ ≤ ((𝔼 x, D x * |F x| ^ (2 ^ n)) / (𝔼 x, D x)) * (𝔼 x, D x) ^ (2 ^ n) := hweighted
      _ = (𝔼 x, D x) ^ (2 ^ n - 1) * (𝔼 x, D x * |F x| ^ (2 ^ n)) := by
        rw [hfactor]
        field_simp [hm]
      _ ≤ (𝔼 x, D x) ^ (2 ^ n - 1) * (B * (𝔼 x, |F x| ^ (2 ^ n))) :=
        mul_le_mul_of_nonneg_left hmoment (pow_nonneg hmean _)
      _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem expect_single_slope {R : Type*} [Ring R] [Fintype R] (a : R) (f : R → ℝ) :
    (𝔼 x, 𝔼 d, f (x + a * d)) = 𝔼 x, f x := by
  rw [Finset.expect_comm]
  have h (d : R) : (𝔼 x, f (x + a * d)) = 𝔼 x, f x := by
    apply Fintype.expect_equiv (Equiv.addRight (a * d))
    intro x
    rfl
  simp only [h, Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotGridFactor_root {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (x d : R) :
    pivotGridFactor v slope f z x d = pivotRootFactor v slope f z (x + slope * d) := rfl

theorem pivotRootFactor_nonneg {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (hf : ∀ x, 0 ≤ f x)
    (z : Fin l → Fin q → R) (w : R) : 0 ≤ pivotRootFactor v slope f z w :=
  Finset.prod_nonneg (fun _ _ => hf _)

theorem pivotRootFactor_le_exp {R : Type*} [CommRing R] {l q : ℕ} {p : ℝ}
    (v : Fin l → R) (slope : R) (f : R → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p)
    (z : Fin l → Fin q → R) (w : R) :
    pivotRootFactor v slope f z w ≤ Real.exp ((q ^ l : ℕ) * p) := by
  calc
    _ ≤ ∏ _beta : Fin l → Fin q, Real.exp p :=
      Finset.prod_le_prod (fun beta _ => (hf _).1) (fun beta _ => (hf _).2)
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivot_weighted_dyadic_step {R Z : Type*} [CommRing R] [Fintype R]
    [Fintype Z] [Nonempty Z] (n : ℕ) (p : R) (D : Z → R → ℝ) (H : Z → R → R → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z w, 0 ≤ D z w) (hcap : ∀ z w, D z w ≤ B) :
    |𝔼 z, 𝔼 x, 𝔼 d, D z (x + p * d) * H z x d| ^ (2 ^ (n + 1)) ≤
      (𝔼 z, 𝔼 w, D z w) ^ (2 ^ (n + 1) - 1) * B *
        (𝔼 z, 𝔼 x, 𝔼 d, 𝔼 t : Fin (2 ^ (n + 1)) → R, ∏ i, H z (x - p * t i) (d + t i)) := by
  have heven : Even (2 ^ (n + 1)) := by
    refine ⟨2 ^ n, ?_⟩
    rw [pow_succ]
    omega
  have hchange (z : Z) :
      (𝔼 x, 𝔼 d, D z (x + p * d) * H z x d) =
        𝔼 w, D z w * (𝔼 d, H z (w - p * d) d) := by
    rw [expect_pivot_change p]
    simp only [sub_add_cancel, ← Finset.mul_expect]
  let D' : Z × R → ℝ := fun u => D u.1 u.2
  let H' : Z × R → ℝ := fun u => 𝔼 d, H u.1 (u.2 - p * d) d
  have h := weighted_dyadic_holder (n + 1) D' H' hB (fun u => hD u.1 u.2) (fun u => hcap u.1 u.2)
  have hm (z : Z) := pivot_even_moment (2 ^ (n + 1)) heven p (H z)
  simpa only [D', H', expect_prod_split, hchange, hm] using h

end Erdos3

end

section

namespace Erdos3

theorem PivotCompatible.cons_erase {I R : Type*} [DecidableEq I] [CommRing R] {l : ℕ}
    {v : Fin l → R} {S : Finset I} {slopes : I → R} {a b : R}
    (h : PivotCompatible v S slopes a b) {i : I} (hi : i ∈ S) :
    PivotCompatible (Fin.cons (slopes i) v) (S.erase i) slopes a b := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro j hj
    exact h.2.1 j (Finset.mem_of_mem_erase hj)
  · intro j hj k hk hjk
    exact h.2.2.1 j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨(h.2.1 i hi).1, (h.2.1 i hi).2, ?_⟩
      intro k hk
      exact h.2.2.1 k (Finset.mem_of_mem_erase hk) i hi (Finset.ne_of_mem_erase hk)
    · exact ⟨(h.2.2.2 j).1, (h.2.2.2 j).2.1,
        fun k hk => (h.2.2.2 j).2.2 k (Finset.mem_of_mem_erase hk)⟩

theorem pivotCompatible_zero {I R : Type*} [CommRing R]
    (v : Fin 0 → R) (S : Finset I) (slopes : I → R) (a b : R)
    (hab : IsUnit (b - a))
    (hends : ∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i))
    (hpairs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) :
    PivotCompatible v S slopes a b :=
  ⟨hab, hends, hpairs, fun j => Fin.elim0 j⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotCellForm_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot slope : R) (z : Fin l → Fin q → R) (t : Fin q → R)
    (x d : R) (i : Fin q) (beta : Fin l → Fin q) :
    pivotCellForm (Fin.cons pivot v) slope (Fin.cons t z) x d (Fin.cons i beta) =
      pivotCellForm v slope z (x - pivot * t i) (d + t i) beta := by
  simp only [pivotCellForm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

theorem pivotGridFactor_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot slope : R) (f : R → ℝ) (z : Fin l → Fin q → R) (t : Fin q → R)
    (x d : R) :
    pivotGridFactor (Fin.cons pivot v) slope f (Fin.cons t z) x d =
      ∏ i : Fin q, pivotGridFactor v slope f z (x - pivot * t i) (d + t i) := by
  unfold pivotGridFactor
  rw [prod_dependent_fin_cons]
  simp only [pivotCellForm_cons]
  rw [Finset.prod_comm]

theorem pivotKernelFactor_cons {R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot a b : R) (parameter : ℝ) (f g : R → ℝ)
    (z : Fin l → Fin q → R) (t : Fin q → R) (x d : R) :
    pivotKernelFactor (Fin.cons pivot v) a b parameter f g (Fin.cons t z) x d =
      ∏ i : Fin q, pivotKernelFactor v a b parameter f g z (x - pivot * t i) (d + t i) := by
  unfold pivotKernelFactor
  rw [prod_dependent_fin_cons]
  simp only [pivotCellForm_cons]
  rw [Finset.prod_comm]

theorem pivotStageIntegrand_cons {I R : Type*} [CommRing R] {l q : ℕ}
    (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (t : Fin q → R) (x d : R) :
    pivotStageIntegrand (Fin.cons pivot v) S slopes mu a b parameter f g (Fin.cons t z) x d =
      ∏ i : Fin q, pivotStageIntegrand v S slopes mu a b parameter f g z
        (x - pivot * t i) (d + t i) := by
  simp only [pivotStageIntegrand, pivotGridFactor_cons, pivotKernelFactor_cons, Finset.prod_mul_distrib]
  rw [Finset.prod_comm]

theorem pivotStageIntegrand_peel {I R : Type*} [DecidableEq I] [CommRing R] {l q : ℕ}
    (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin l → Fin q → R) (x d : R)
    {i : I} (hi : i ∈ S) :
    pivotStageIntegrand v S slopes mu a b parameter f g z x d =
      pivotRootFactor v (slopes i) (mu i) z (x + slopes i * d) *
        pivotStageIntegrand v (S.erase i) slopes mu a b parameter f g z x d := by
  unfold pivotStageIntegrand
  rw [← Finset.mul_prod_erase S _ hi, pivotGridFactor_root]
  ring

theorem pivotStageCount_cons {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (pivot : R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) (Fin.cons pivot v) S slopes mu a b parameter f g =
      𝔼 z : Fin l → Fin q → R, 𝔼 x, 𝔼 d, 𝔼 t : Fin q → R,
        ∏ i : Fin q, pivotStageIntegrand v S slopes mu a b parameter f g z
          (x - pivot * t i) (d + t i) := by
  rw [pivotStageCount, expect_fin_cons]
  simp only [pivotStageIntegrand_cons]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro z _
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotStageCount_step {I R : Type*} [DecidableEq I] [CommRing R] [Fintype R]
    {l : ℕ} (n : ℕ) (v : Fin l → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) {i : I} (hi : i ∈ S) {p : ℝ}
    (hmu : ∀ x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) :
    |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ^ (2 ^ (n + 1)) ≤
      (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w, pivotRootFactor v (slopes i) (mu i) z w) ^
        (2 ^ (n + 1) - 1) * Real.exp (((2 ^ (n + 1)) ^ l : ℕ) * p) *
      pivotStageCount (q := 2 ^ (n + 1)) (Fin.cons (slopes i) v) (S.erase i) slopes mu a b parameter f g := by
  let D : (Fin l → Fin (2 ^ (n + 1)) → R) → R → ℝ := pivotRootFactor v (slopes i) (mu i)
  let H : (Fin l → Fin (2 ^ (n + 1)) → R) → R → R → ℝ :=
    pivotStageIntegrand v (S.erase i) slopes mu a b parameter f g
  have h := pivot_weighted_dyadic_step n (slopes i) D H (Real.exp_nonneg _)
    (fun z w => pivotRootFactor_nonneg v (slopes i) (mu i) (fun x => (hmu x).1) z w)
    (fun z w => pivotRootFactor_le_exp v (slopes i) (mu i) hmu z w)
  have hleft : (𝔼 z, 𝔼 x, 𝔼 d, D z (x + slopes i * d) * H z x d) =
      pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g := by
    unfold pivotStageCount
    apply Finset.expect_congr rfl
    intro z _
    apply Finset.expect_congr rfl
    intro x _
    apply Finset.expect_congr rfl
    intro d _
    exact (pivotStageIntegrand_peel v S slopes mu a b parameter f g z x d hi).symm
  have hright : (𝔼 z, 𝔼 x, 𝔼 d, 𝔼 t : Fin (2 ^ (n + 1)) → R,
      ∏ j, H z (x - slopes i * t j) (d + t j)) =
        pivotStageCount (q := 2 ^ (n + 1)) (Fin.cons (slopes i) v) (S.erase i) slopes mu a b parameter f g := by
    exact (pivotStageCount_cons v (slopes i) (S.erase i) slopes mu a b parameter f g).symm
  rw [hleft, hright] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotGridFactor_zero {R : Type*} [CommRing R] {q : ℕ}
    (v : Fin 0 → R) (slope : R) (f : R → ℝ) (z : Fin 0 → Fin q → R) (x d : R) :
    pivotGridFactor v slope f z x d = f (x + slope * d) := by
  unfold pivotGridFactor
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp [pivotCellForm]

theorem pivotKernelFactor_zero {R : Type*} [CommRing R] {q : ℕ}
    (v : Fin 0 → R) (a b : R) (parameter : ℝ) (f g : R → ℝ) (z : Fin 0 → Fin q → R) (x d : R) :
    pivotKernelFactor v a b parameter f g z x d = countingKernel parameter (f (x + a * d)) (g (x + b * d)) := by
  unfold pivotKernelFactor
  rw [Fintype.prod_subsingleton _ (fun i => Fin.elim0 i)]
  simp [pivotCellForm]

theorem pivotStageCount_zero {I R : Type*} [CommRing R] [Fintype R] {q : ℕ}
    (v : Fin 0 → R) (S : Finset I) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) v S slopes mu a b parameter f g =
      𝔼 x, 𝔼 d, (∏ i ∈ S, mu i (x + slopes i * d)) *
        countingKernel parameter (f (x + a * d)) (g (x + b * d)) := by
  simp only [pivotStageCount, pivotStageIntegrand, pivotGridFactor_zero,
    pivotKernelFactor_zero, Fintype.expect_const]

theorem pivotStageCount_terminal {I R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (hab : IsUnit (b - a)) (parameter : ℝ) (f g : R → ℝ) :
    pivotStageCount (q := q) v (∅ : Finset I) slopes mu a b parameter f g =
      𝔼 z : Fin l → Fin q → R, countingKernelProductAverage parameter
        (fun (beta : Fin l → Fin q) (u : R) => f (u + ∑ j, (a - v j) * z j (beta j)))
        (fun (beta : Fin l → Fin q) (w : R) => g (w + ∑ j, (b - v j) * z j (beta j))) := by
  simp only [pivotStageCount, pivotStageIntegrand, Finset.prod_empty, one_mul]
  apply Finset.expect_congr rfl
  intro z _
  exact expect_two_slopes a b hab (fun u w => ∏ beta : Fin l → Fin q,
    countingKernel parameter (f (u + ∑ j, (a - v j) * z j (beta j)))
      (g (w + ∑ j, (b - v j) * z j (beta j))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PivotGridBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rootGrid_volume (r q l : ℕ) :
    positiveGridVolume (Fin.cons r (fun _ : Fin l => q)) = r * q ^ l := by
  simp [positiveGridVolume, Fin.prod_univ_succ]

theorem pivotRootFactor_mean_grid {R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (hunit : ∀ j, IsUnit (slope - v j)) (f : R → ℝ) :
    (𝔼 z : Fin l → Fin q → R, 𝔼 w, pivotRootFactor v slope f z w) =
      positiveGridMean (Fin.cons 1 (fun _ : Fin l => q)) (fun _ => f) := by
  rw [← scaledRootGrid_mean 1 q l (fun j => slope - v j) hunit (fun _ _ => f)]
  apply Finset.expect_congr rfl
  intro z _
  symm
  rw [expect_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.prod_univ_zero, mul_one,
    Fintype.expect_const, pivotRootFactor]

theorem pivot_boolean_product_mean_grid {R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (hunit : ∀ j, IsUnit (slope - v j)) (f : R → ℝ)
    (choice : (Fin l → Fin q) → Bool) :
    (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
      if choice beta then
        f (u + ∑ j, (slope - v j) * z j (beta j)) *
        f (w + ∑ j, (slope - v j) * z j (beta j)) else 1) =
      positiveGridMean (Fin.cons 2 (fun _ : Fin l => q))
        (fun beta x => if choice (fun j => beta j.succ) then f x else 1) := by
  rw [← scaledRootGrid_mean 2 q l (fun j => slope - v j) hunit
    (fun _ beta x => if choice beta then f x else 1)]
  apply Finset.expect_congr rfl
  intro z _
  symm
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro u _
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro w _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_zero, mul_one,
    Fintype.expect_const]
  apply Finset.prod_congr rfl
  intro beta _
  by_cases h : choice beta
  · simp only [h, ite_true]
  · simp only [h, Bool.false_eq_true, ite_false, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_pivot_grid_bounds (s : ℕ) {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N l q : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N → l ≤ s → 1 ≤ q → (q : ℝ) ≤ C0 * p →
      ∀ (v : Fin l → ZMod N) (slope : ZMod N), (∀ j, IsUnit (slope - v j)) →
      ∀ f : ZMod N → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (𝔼 z : Fin l → Fin q → ZMod N, 𝔼 w, pivotRootFactor v slope f z w) ≤
        (1 + delta) ^ (q ^ l) ∧
      ∀ choice : (Fin l → Fin q) → Bool,
        (𝔼 z : Fin l → Fin q → ZMod N, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
          if choice beta then
            f (u + ∑ j, (slope - v j) * z j (beta j)) *
            f (w + ∑ j, (slope - v j) * z j (beta j)) else 1) ≤
          (1 + delta) ^ (2 * q ^ l) := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_positiveGrid_family_counting s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N l q _ p xi hp hxi hxib hodd hN hl hq hqcap v slope hunit f hf hcompare
  have hrootcap : (2 : ℝ) ≤ C0 * p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC0) (show 0 ≤ p by linarith)]
  have hshape (r : ℕ) (hr : 1 ≤ r) (hr2 : r ≤ 2) :
      ∀ i : Fin (l + 1), 1 ≤ (Fin.cons r (fun _ : Fin l => q) : Fin (l + 1) → ℕ) i ∧
        (((Fin.cons r (fun _ : Fin l => q) : Fin (l + 1) → ℕ) i : ℕ) : ℝ) ≤ C0 * p := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact ⟨hr, (show (r : ℝ) ≤ 2 by exact_mod_cast hr2).trans hrootcap⟩
    · exact ⟨hq, hqcap⟩
  have hbound (r : ℕ) (hr : 1 ≤ r) (hr2 : r ≤ 2)
      (ch : PositiveGridVertex (Fin.cons r (fun _ : Fin l => q)) → Option Unit) :
      positiveGridMean (Fin.cons r (fun _ : Fin l => q))
        (fun beta x => (ch beta).elim 1 (fun _ => f x)) ≤ (1 + delta) ^ (r * q ^ l) := by
    have h := hgrid hp hxi hxib hodd hN (show 1 ≤ l + 1 by omega)
      (show l + 1 ≤ s + 1 by omega) (Fin.cons r (fun _ : Fin l => q)) (hshape r hr hr2)
      (fun _ : Unit => f) (fun _ => hf) (fun _ => @hcompare) ch
    simpa only [rootGrid_volume] using h
  constructor
  · rw [pivotRootFactor_mean_grid v slope hunit]
    simpa only [Option.elim_some, one_mul] using hbound 1 (by omega) (by omega) (fun _ => some ())
  · intro choice
    rw [pivot_boolean_product_mean_grid v slope hunit f choice]
    let ch : PositiveGridVertex (Fin.cons 2 (fun _ : Fin l => q)) → Option Unit :=
      fun beta => if choice (fun j => beta j.succ) then some () else none
    have h := hbound 2 (by omega) (by omega) ch
    have heq : (fun beta x => (ch beta).elim 1 (fun _ => f x)) =
        (fun (beta : PositiveGridVertex (Fin.cons 2 (fun _ : Fin l => q))) x =>
          if choice (fun j => beta j.succ) then f x else 1) := by
      funext beta x
      dsimp only [ch]
      split_ifs <;> rfl
    rw [heq] at h
    exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PivotNativeIteration
namespace OAI

section

namespace Erdos3

theorem pivotIterationBound_nonneg (q r m : ℕ) (p : ℝ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ pivotIterationBound q r m p B :=
  mul_nonneg (Real.exp_nonneg _) (pow_nonneg hB _)

theorem pivotIterationBound_zero (q m : ℕ) (p B : ℝ) :
    pivotIterationBound q 0 m p B = B ^ (2 * m) := by
  simp [pivotIterationBound]

theorem pivotIterationBound_step {q : ℕ} (hq : 1 ≤ q) (r m : ℕ) (p : ℝ)
    {B : ℝ} (hB : 1 ≤ B) :
    (B ^ m) ^ (q - 1) * Real.exp ((m : ℝ) * p) *
        pivotIterationBound q r (q * m) p B ≤
      (pivotIterationBound q (r + 1) m p B) ^ q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : (m : ℝ) * p + r * p * (q * m) / q =
      q * (((r + 1 : ℕ) : ℝ) * p * m / q) := by
    push_cast
    field_simp [hq0]
    ring
  have hn : m * (q - 1) + (r + 2) * (q * m) ≤ ((r + 1 + 2) * m) * q := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
    nlinarith
  unfold pivotIterationBound
  simp only [Nat.cast_mul]
  rw [mul_pow, ← Real.exp_nat_mul]
  calc
    (B ^ m) ^ (q - 1) * Real.exp ((m : ℝ) * p) *
        (Real.exp ((r : ℝ) * p * (q * m) / q) * B ^ ((r + 2) * (q * m))) =
      (Real.exp ((m : ℝ) * p) * Real.exp ((r : ℝ) * p * (q * m) / q)) *
        ((B ^ m) ^ (q - 1) * B ^ ((r + 2) * (q * m))) := by ring
    _ = Real.exp (q * (((r + 1 : ℕ) : ℝ) * p * m / q)) *
        B ^ (m * (q - 1) + (r + 2) * (q * m)) := by
      rw [← Real.exp_add, he, ← pow_mul, ← pow_add]
    _ ≤ Real.exp (q * (((r + 1 : ℕ) : ℝ) * p * m / q)) *
        B ^ (((r + 1 + 2) * m) * q) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hn) (Real.exp_nonneg _)
    _ = _ := by rw [pow_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem pivotStageCount_terminal_le {I R : Type*} [CommRing R] [Fintype R]
    {l q : ℕ} (v : Fin l → R) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (hab : IsUnit (b - a)) {parameter A : ℝ}
    (hparameter : 0 ≤ parameter) (hparameter1 : parameter ≤ 1) (hA : 0 ≤ A)
    (f g : R → ℝ)
    (hf : ∀ choice : (Fin l → Fin q) → Bool,
      (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
        if choice beta then
          f (u + ∑ j, (a - v j) * z j (beta j)) *
          f (w + ∑ j, (a - v j) * z j (beta j)) else 1) ≤ A)
    (hg : ∀ choice : (Fin l → Fin q) → Bool,
      (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
        if choice beta then
          g (u + ∑ j, (b - v j) * z j (beta j)) *
          g (w + ∑ j, (b - v j) * z j (beta j)) else 1) ≤ A) :
    |pivotStageCount (q := q) v (∅ : Finset I) slopes mu a b parameter f g| ≤ A := by
  rw [pivotStageCount_terminal v slopes mu a b hab]
  exact countingKernelProductAverage_outer_abs_le hparameter hparameter1 hA _ _ hf hg

theorem pivotStageCount_iterate {I R : Type*} [DecidableEq I] [CommRing R] [Fintype R]
    (s n : ℕ) (slopes : I → R) (mu : I → R → ℝ)
    (a b : R) (parameter : ℝ) (f g : R → ℝ) {p B : ℝ} (hB : 1 ≤ B)
    (hmu : ∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p)
    (hroot : ∀ {l : ℕ}, l ≤ s → ∀ (v : Fin l → R) (i : I),
      (∀ j, IsUnit (slopes i - v j)) →
      (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
        pivotRootFactor v (slopes i) (mu i) z w) ≤ B ^ ((2 ^ (n + 1)) ^ l))
    (hterminal : ∀ {l : ℕ}, l ≤ s → ∀ (v : Fin l → R),
      PivotCompatible v (∅ : Finset I) slopes a b →
      |pivotStageCount (q := 2 ^ (n + 1)) v (∅ : Finset I) slopes mu a b parameter f g| ≤
        B ^ (2 * (2 ^ (n + 1)) ^ l))
    {l : ℕ} (v : Fin l → R) (S : Finset I) (hsize : l + S.card ≤ s)
    (hcompatible : PivotCompatible v S slopes a b) :
    |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ≤
      pivotIterationBound (2 ^ (n + 1)) S.card ((2 ^ (n + 1)) ^ l) p B := by
  have hq : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  induction S using Finset.induction_on generalizing l with
  | empty =>
      simpa only [Finset.card_empty, pivotIterationBound_zero] using
        hterminal (by simpa only [Finset.card_empty, add_zero] using hsize) v hcompatible
  | @insert i S hi ih =>
      have hmem : i ∈ insert i S := Finset.mem_insert_self i S
      have hc := hcompatible.cons_erase hmem
      rw [Finset.erase_insert hi] at hc
      have hs : (l + 1) + S.card ≤ s := by
        rw [Finset.card_insert_of_notMem hi] at hsize
        omega
      have hn := ih (Fin.cons (slopes i) v) hs hc
      have hrep : (2 ^ (n + 1)) ^ (l + 1) = 2 ^ (n + 1) * (2 ^ (n + 1)) ^ l := by
        rw [pow_succ, Nat.mul_comm]
      rw [hrep] at hn
      have hr := pivotStageCount_step n v (insert i S) slopes mu a b parameter f g hmem (hmu i)
      rw [Finset.erase_insert hi] at hr
      have hd := hroot (show l ≤ s by omega) v i
        (fun j => (hcompatible.2.2.2 j).2.2 i hmem)
      have hd0 : 0 ≤ (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
          pivotRootFactor v (slopes i) (mu i) z w) :=
        Finset.expect_nonneg (fun z _ => Finset.expect_nonneg
          (fun w _ => pivotRootFactor_nonneg v (slopes i) (mu i) (fun x => (hmu i x).1) z w))
      have hcoef := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hd0 hd (2 ^ (n + 1) - 1))
        (Real.exp_nonneg (((2 ^ (n + 1)) ^ l : ℕ) * p))
      have hcoef0 : 0 ≤ (𝔼 z : Fin l → Fin (2 ^ (n + 1)) → R, 𝔼 w,
          pivotRootFactor v (slopes i) (mu i) z w) ^ (2 ^ (n + 1) - 1) *
          Real.exp (((2 ^ (n + 1)) ^ l : ℕ) * p) :=
        mul_nonneg (pow_nonneg hd0 _) (Real.exp_nonneg _)
      have hpower := hr.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) hcoef0).trans
        (mul_le_mul hcoef hn (abs_nonneg _)
          (mul_nonneg (pow_nonneg (pow_nonneg hB0 _) _) (Real.exp_nonneg _))))
      have hfinal := hpower.trans
        (pivotIterationBound_step hq S.card ((2 ^ (n + 1)) ^ l) p hB)
      rw [Finset.card_insert_of_notMem hi]
      exact le_of_pow_le_pow_left₀ (by omega)
        (pivotIterationBound_nonneg _ _ _ _ hB0) hfinal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_pivot_stage_bound (s : ℕ) {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ n : ℕ, ((2 ^ (n + 1) : ℕ) : ℝ) ≤ C0 * p →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ)
        (a b : ZMod N) (parameter : ℝ) (f g : ZMod N → ℝ),
      0 ≤ parameter → parameter ≤ 1 →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) g (fun _ => 1 + xi) →
      ∀ {l : ℕ} (v : Fin l → ZMod N) (S : Finset I), l + S.card ≤ s →
        PivotCompatible v S slopes a b →
        |pivotStageCount (q := 2 ^ (n + 1)) v S slopes mu a b parameter f g| ≤
          pivotIterationBound (2 ^ (n + 1)) S.card ((2 ^ (n + 1)) ^ l) p (1 + delta) := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_pivot_grid_bounds s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hodd hN n hqcap I _ slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare l v S hsize hcompatible
  have hq : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by omega)
  have hB0 : 0 ≤ 1 + delta := by linarith
  apply pivotStageCount_iterate s n slopes mu a b parameter f g (by linarith) hmu
    (hroot := ?_) (hterminal := ?_) v S hsize hcompatible
  · intro k hk u i hunit
    exact (hgrid hp hxi hxib hodd hN hk hq hqcap u (slopes i) hunit (mu i)
      (hmu i) (@hcompare i)).1
  · intro k hk u hc
    apply pivotStageCount_terminal_le u slopes mu a b hc.1 hparameter hparameter1
      (pow_nonneg hB0 _) f g
    · exact (hgrid hp hxi hxib hodd hN hk hq hqcap u a
        (fun j => (hc.2.2.2 j).1) f hf hfcompare).2
    · exact (hgrid hp hxi hxib hodd hN hk hq hqcap u b
        (fun j => (hc.2.2.2 j).2.1) g hg hgcompare).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CountingDeficitDetection
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem countingKernelAverage_one {X : Type*} [Fintype X] (w f g : X → ℝ) :
    countingKernelAverage 1 w f g = 𝔼 x, w x * f x * g x := by
  simp only [countingKernelAverage, countingKernel_one, mul_assoc]

theorem countingKernelAverage_quarter {X : Type*} [Fintype X] (w f g : X → ℝ) :
    countingKernelAverage (1 / 4) w f g =
      (3 / 8) * (𝔼 x, w x) + (3 / 8) * (𝔼 x, w x * f x) +
      (3 / 8) * (𝔼 x, w x * g x) - (1 / 8) * (𝔼 x, w x * f x * g x) := by
  have hpoint (x) : w x * countingKernel (1 / 4) (f x) (g x) =
      (3 / 8) * w x + (3 / 8) * (w x * f x) +
      (3 / 8) * (w x * g x) - (1 / 8) * (w x * f x * g x) := by
    rw [countingKernel_quarter]
    ring
  simp only [countingKernelAverage, hpoint, Finset.expect_add_distrib,
    Finset.expect_sub_distrib, ← Finset.mul_expect]

theorem quarterKernel_deficit_surplus {A00 A10 A01 A11 tau : ℝ}
    (h00 : |A00 - 1| ≤ tau / 18) (h10 : |A10 - 1| ≤ tau / 18)
    (h01 : |A01 - 1| ≤ tau / 18) (h11 : A11 < 1 - tau) :
    1 + tau / 16 < (3 / 8) * A00 + (3 / 8) * A10 + (3 / 8) * A01 - (1 / 8) * A11 := by
  obtain ⟨h00l, _⟩ := abs_le.mp h00
  obtain ⟨h10l, _⟩ := abs_le.mp h10
  obtain ⟨h01l, _⟩ := abs_le.mp h01
  linarith

theorem exists_countingKernel_surplus {X : Type*} [Fintype X] {tau : ℝ} (htau : 0 < tau)
    (w f g : X → ℝ) (h00 : |(𝔼 x, w x) - 1| ≤ tau / 18)
    (h10 : |(𝔼 x, w x * f x) - 1| ≤ tau / 18)
    (h01 : |(𝔼 x, w x * g x) - 1| ≤ tau / 18)
    (hbad : tau < |(𝔼 x, w x * f x * g x) - 1|) :
    ∃ b : ℝ, (b = 1 ∨ b = 1 / 4) ∧ 1 + tau / 16 < countingKernelAverage b w f g := by
  rcases lt_abs.mp hbad with hsurplus | hdeficit
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [countingKernelAverage_one]
    linarith
  · refine ⟨1 / 4, Or.inr rfl, ?_⟩
    rw [countingKernelAverage_quarter]
    exact quarterKernel_deficit_surplus h00 h10 h01 (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DyadicCountingParameters
namespace OAI

section

namespace Erdos3

open Filter Topology

theorem exists_counting_kernel_parameters (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ p : ℝ, 2 ≤ p → ∃ n : ℕ, ((2 ^ (n + 1) : ℕ) : ℝ) ≤ C0 * p ∧
        ∀ r : ℕ, r ≤ s →
          pivotIterationBound (2 ^ (n + 1)) r 1 p (1 + delta) < 1 + tau := by
  have hcontinuous : ContinuousAt
      (fun x : ℝ => Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2)) 0 := by fun_prop
  have htend : Tendsto (fun x : ℝ => Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2))
      (𝓝 0) (𝓝 1) := by simpa using hcontinuous.tendsto
  have heventually : ∀ᶠ x : ℝ in 𝓝 0,
      Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2) < 1 + tau :=
    htend.eventually_lt_const (by linarith)
  obtain ⟨a, ha, hball⟩ := Metric.eventually_nhds_iff_ball.mp heventually
  let delta := min a 1 / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta < 1 := by
    dsimp [delta]
    have h := min_le_right a (1 : ℝ)
    linarith
  have hdeltaa : delta < a := by
    dsimp [delta]
    have h := min_le_left a (1 : ℝ)
    linarith
  have hsmall : Real.exp ((s : ℝ) * delta) * (1 + delta) ^ (s + 2) < 1 + tau :=
    hball delta (by simpa [Real.dist_eq, abs_of_pos hdelta] using hdeltaa)
  refine ⟨delta, hdelta, 2 / delta, ?_, ?_⟩
  · apply (le_div_iff₀ hdelta).2
    linarith
  · intro p hp
    have hp0 : 0 < p := by linarith
    have hnear : 1 ≤ p / delta := by
      apply (le_div_iff₀ hdelta).2
      linarith
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hnear (show (1 : ℝ) < 2 by norm_num)
    have hq0 : 0 < ((2 ^ (n + 1) : ℕ) : ℝ) := by positivity
    have hqcap : ((2 ^ (n + 1) : ℕ) : ℝ) ≤ (2 / delta) * p := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      calc
        (2 : ℝ) ^ n * 2 ≤ (p / delta) * 2 := mul_le_mul_of_nonneg_right hlo (by norm_num)
        _ = _ := by ring
    have hpq : p / ((2 ^ (n + 1) : ℕ) : ℝ) ≤ delta := by
      apply (div_le_iff₀ hq0).2
      have hhi' : p / delta < ((2 ^ (n + 1) : ℕ) : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hhi
      have h := (div_lt_iff₀ hdelta).mp hhi'
      nlinarith
    refine ⟨n, hqcap, ?_⟩
    intro r hrs
    have hexp : (r : ℝ) * p / ((2 ^ (n + 1) : ℕ) : ℝ) ≤ s * delta := by
      rw [mul_div_assoc]
      exact mul_le_mul (by exact_mod_cast hrs) hpq (le_of_lt (div_pos hp0 hq0))
        (Nat.cast_nonneg s)
    have hpow : (1 + delta) ^ (r + 2) ≤ (1 + delta) ^ (s + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    unfold pivotIterationBound
    simp only [Nat.cast_one, mul_one]
    exact (mul_le_mul (Real.exp_le_exp.mpr hexp) hpow
      (pow_nonneg (by linarith) _) (Real.exp_nonneg _)).trans_lt hsmall

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteKernelCounting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem subset_counting_error_scale {m n : ℕ} (hmn : m < n) {delta : ℝ} (hdelta : 0 ≤ delta) :
    (18 : ℝ) ^ m * delta ≤ ((18 : ℝ) ^ n * delta) / 18 := by
  calc
    (18 : ℝ) ^ m * delta = ((18 : ℝ) ^ (m + 1) * delta) / 18 := by rw [pow_succ]; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hdelta)
      (by norm_num)

theorem finite_products_near_one_of_kernel_bound {I X : Type*}
    [DecidableEq I] [Fintype X] [Nonempty X] (s : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (F : I → X → ℝ) (hmean : ∀ i, |(𝔼 x, F i x) - 1| ≤ delta)
    (hkernel : ∀ (S : Finset I), S.card ≤ s → ∀ i j : I, i ∉ S → j ∉ S → i ≠ j →
      ∀ b : ℝ, (b = 1 ∨ b = 1 / 4) →
        countingKernelAverage b (fun x => ∏ k ∈ S, F k x) (F i) (F j) ≤ 1 + delta / 16)
    (T : Finset I) (hT : T.card ≤ s + 2) :
    |(𝔼 x, ∏ i ∈ T, F i x) - 1| ≤ (18 : ℝ) ^ T.card * delta := by
  induction T using Finset.strongInductionOn
  rename_i T ih
  rcases T.eq_empty_or_nonempty with rfl | hnonempty
  · simp only [Finset.prod_empty, Fintype.expect_const, sub_self, abs_zero,
      Finset.card_empty, pow_zero, one_mul]
    exact le_of_lt hdelta
  by_cases hsmall : T.card ≤ 1
  · obtain ⟨i, hi⟩ := hnonempty
    have heq : T = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun j hj => Finset.card_le_one.mp hsmall j hj i hi⟩
    rw [heq]
    simp only [Finset.prod_singleton, Finset.card_singleton, pow_one]
    exact (hmean i).trans (by linarith)
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  let S := (T.erase i).erase j
  have hj' : j ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hSi : i ∉ S := by simp [S]
  have hSj : j ∉ S := by simp [S]
  have hSji : insert j S = T.erase i := Finset.insert_erase hj'
  have hSij : insert i S = T.erase j := by
    dsimp [S]
    rw [Finset.erase_right_comm, Finset.insert_erase (Finset.mem_erase.mpr ⟨hij, hi⟩)]
  have hform : T = insert i (insert j S) := by rw [hSji, Finset.insert_erase hi]
  have hScard : S.card ≤ s := by
    dsimp [S]
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi]
    omega
  have hproper (U : Finset I) (hU : U ⊂ T) :
      |(𝔼 x, ∏ k ∈ U, F k x) - 1| ≤ ((18 : ℝ) ^ T.card * delta) / 18 :=
    (ih U hU ((Finset.card_le_card (le_of_lt hU)).trans hT)).trans
      (subset_counting_error_scale (Finset.card_lt_card hU) (le_of_lt hdelta))
  have h00 := hproper S (lt_of_le_of_lt (Finset.erase_subset j (T.erase i))
    (Finset.erase_ssubset hi))
  have h10 : |(𝔼 x, (∏ k ∈ S, F k x) * F i x) - 1| ≤
      ((18 : ℝ) ^ T.card * delta) / 18 := by
    have h := hproper (insert i S) (by rw [hSij]; exact Finset.erase_ssubset hj)
    simpa only [Finset.prod_insert hSi, mul_comm] using h
  have h01 : |(𝔼 x, (∏ k ∈ S, F k x) * F j x) - 1| ≤
      ((18 : ℝ) ^ T.card * delta) / 18 := by
    have h := hproper (insert j S) (by rw [hSji]; exact Finset.erase_ssubset hi)
    simpa only [Finset.prod_insert hSj, mul_comm] using h
  have hprod (x : X) : (∏ k ∈ T, F k x) = (∏ k ∈ S, F k x) * F i x * F j x := by
    rw [hform, Finset.prod_insert (by simp [hij, hSi]), Finset.prod_insert hSj]
    ring
  by_contra! hbad
  simp only [hprod] at hbad
  obtain ⟨b, hb, hsurplus⟩ := exists_countingKernel_surplus
    (mul_pos (pow_pos (by norm_num) _) hdelta) (fun x => ∏ k ∈ S, F k x)
    (F i) (F j) h00 h10 h01 hbad
  have hu := hkernel S hScard i j hSi hSj hij b hb
  have hscale : delta ≤ (18 : ℝ) ^ T.card * delta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (show (1 : ℝ) ≤ 18 by norm_num)) (le_of_lt hdelta)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProgressionKernelBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_progression_kernel_bound (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ)
        (a b : ZMod N) (parameter : ℝ) (f g : ZMod N → ℝ),
      0 ≤ parameter → parameter ≤ 1 →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) g (fun _ => 1 + xi) →
      ∀ S : Finset I, S.card ≤ s → IsUnit (b - a) →
        (∀ i ∈ S, IsUnit (a - slopes i) ∧ IsUnit (b - slopes i)) →
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → IsUnit (slopes i - slopes j)) →
        |𝔼 x, 𝔼 d, (∏ i ∈ S, mu i (x + slopes i * d)) *
          countingKernel parameter (f (x + a * d)) (g (x + b * d))| < 1 + tau := by
  obtain ⟨delta, hdelta, C0, hC0, hparameters⟩ := exists_counting_kernel_parameters s htau
  obtain ⟨C, hC, xi0, hxi0, hstage⟩ := exists_pivot_stage_bound s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N _ p xi hp hxi hxib hodd hN I _ slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare S hS hab hends hpairs
  obtain ⟨n, hqcap, hsmall⟩ := hparameters p hp
  let v : Fin 0 → ZMod N := Fin.elim0
  have hc := pivotCompatible_zero v S slopes a b hab hends hpairs
  have h := hstage hp hxi hxib hodd hN n hqcap slopes mu a b parameter f g
    hparameter hparameter1 hmu hcompare hf hfcompare hg hgcompare v S
    (by simpa only [zero_add] using hS) hc
  rw [pivotStageCount_zero] at h
  simpa only [pow_zero] using h.trans_lt (hsmall S.card hS)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MaskedCenteredCounting
namespace OAI

universe u

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_progression_counting_s2_oai (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N →
      ∀ {I : Type} [DecidableEq I] (slopes : I → ZMod N) (mu : I → ZMod N → ℝ),
      (∀ i j, i ≠ j → IsUnit (slopes i - slopes j)) →
      (∀ i x, 0 ≤ mu i x ∧ mu i x ≤ Real.exp p) →
      (∀ i, |(𝔼 x, mu i x) - 1| ≤ 2 * xi) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) (mu i) (fun _ => 1 + xi)) →
      ∀ T : Finset I, T.card ≤ s + 2 →
        |(𝔼 x, 𝔼 d, ∏ i ∈ T, mu i (x + slopes i * d)) - 1| ≤ tau := by
  let delta := tau / (18 : ℝ) ^ (s + 2)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, hC, xi1, hxi1, hkernel⟩ := exists_progression_kernel_bound s
    (show 0 < delta / 16 by positivity)
  refine ⟨C, hC, min xi1 (delta / 2), lt_min hxi1 (by positivity), ?_⟩
  intro N _ p xi hp hxi hxib hodd hN I _ slopes mu hsep hmu hmean hcompare T hT
  have hxi1b : xi ≤ xi1 := hxib.trans (min_le_left _ _)
  have hxid : 2 * xi ≤ delta := by
    have h := hxib.trans (min_le_right xi1 (delta / 2))
    linarith
  let F : I → (ZMod N × ZMod N) → ℝ := fun i z => mu i (z.1 + slopes i * z.2)
  have hmeanF (i : I) : |(𝔼 z, F i z) - 1| ≤ delta := by
    dsimp only [F]
    rw [expect_prod_split, expect_single_slope]
    exact (hmean i).trans hxid
  have hkernelF (S : Finset I) (hS : S.card ≤ s) (i j : I)
      (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) (b : ℝ) (hb : b = 1 ∨ b = 1 / 4) :
      countingKernelAverage b (fun z => ∏ k ∈ S, F k z) (F i) (F j) ≤ 1 + delta / 16 := by
    have hb0 : 0 ≤ b := by rcases hb with rfl | rfl <;> norm_num
    have hb1 : b ≤ 1 := by rcases hb with rfl | rfl <;> norm_num
    have h := hkernel hp hxi hxi1b hodd hN slopes mu (slopes i) (slopes j) b (mu i) (mu j)
      hb0 hb1 hmu hcompare (hmu i) (@hcompare i) (hmu j) (@hcompare j) S hS
      (hsep j i (Ne.symm hij))
      (fun k hk => ⟨hsep i k (by rintro rfl; exact hi hk),
        hsep j k (by rintro rfl; exact hj hk)⟩)
      (fun k _ l _ hkl => hsep k l hkl)
    unfold countingKernelAverage
    rw [expect_prod_split]
    exact (le_abs_self _).trans (le_of_lt h)
  have h := finite_products_near_one_of_kernel_bound s hdelta F hmeanF hkernelF T hT
  dsimp only [F] at h
  rw [expect_prod_split] at h
  apply h.trans
  calc
    (18 : ℝ) ^ T.card * delta ≤ (18 : ℝ) ^ (s + 2) * delta :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hT) (le_of_lt hdelta)
    _ = tau := by dsimp [delta]; field_simp

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_positive_progression_counting_s2_oai := @OAI.Erdos3.exists_positive_progression_counting_s2_oai
