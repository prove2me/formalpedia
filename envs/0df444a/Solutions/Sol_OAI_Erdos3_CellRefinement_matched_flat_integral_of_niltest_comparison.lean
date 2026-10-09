-- Prove2me | solution 1 for OAI.Erdos3.CellRefinement.matched_flat_integral_of_niltest_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:46:54.142252+00:00
-- url     : https://prove2.me/submissions/24e748bb-89f5-4304-bc08-f92bec3a1e39

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B041

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedAverageScaleOrder
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem localizedAverageScale_spec (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    0 < localizedAverageScale rank R epsilon ∧
      localizedAverageScale rank R epsilon ≤ 1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      R * (400 * (max rank 1 : ℕ) * (localizedAverageScale rank R epsilon : ℝ)) ≤ epsilon := by
  let d : ℝ := (max rank 1 : ℕ)
  let r : ℝ := min (1 / (200 * d)) (epsilon / (400 * d * (R + 1)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hcast : (localizedAverageScale rank R epsilon : ℝ) = r := Real.coe_toNNReal r hr.le
  refine ⟨Real.toNNReal_pos.mpr hr, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    push_cast
    rw [hcast]
    have hdcast : max (rank : ℝ) 1 = d := by simp [d]
    rw [hdcast]
    have h : r ≤ 1 / (200 * d) := min_le_left _ _
    convert h using 1
    ring
  · rw [hcast]
    change R * (400 * d * r) ≤ epsilon
    have h : r * (400 * d * (R + 1)) ≤ epsilon :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [mul_nonneg hr.le hd.le]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LocalizedAverageScaleBudget
namespace OAI

section

namespace Erdos3

theorem localizedAverageScale_exp_lower (rank : ℕ) {W A E : ℝ}
    (hW : 0 ≤ W) (hWA : W ≤ Real.exp A) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Real.exp (-((rank : ℝ) + A + E + 1600)) ≤
      (localizedAverageScale rank W (Real.exp (-E) / 2) : ℝ) := by
  let m : ℝ := (max rank 1 : ℕ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hmexp : m ≤ Real.exp (rank : ℝ) := by
    apply le_trans _ (Real.add_one_le_exp (rank : ℝ))
    dsimp [m]
    exact_mod_cast (show max rank 1 ≤ rank + 1 by omega)
  have hWexp : W + 1 ≤ 2 * Real.exp A := by
    linarith [Real.one_le_exp hA]
  have hden : 800 * m * (W + 1) ≤ Real.exp ((rank : ℝ) + A + 1600) := by
    calc
      _ ≤ 800 * Real.exp (rank : ℝ) * (2 * Real.exp A) := by gcongr
      _ = 1600 * Real.exp ((rank : ℝ) + A) := by rw [Real.exp_add]; ring
      _ ≤ Real.exp 1600 * Real.exp ((rank : ℝ) + A) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 1600]
      _ = Real.exp ((rank : ℝ) + A + 1600) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hscaled : Real.exp (-((rank : ℝ) + A + E + 1600)) *
      (800 * m * (W + 1)) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp (-((rank : ℝ) + A + E + 1600)) *
          Real.exp ((rank : ℝ) + A + 1600) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmin : 0 ≤ min (1 / (200 * m)) ((Real.exp (-E) / 2) / (400 * m * (W + 1))) := by
    exact le_of_lt (lt_min (by positivity) (by positivity))
  change Real.exp (-((rank : ℝ) + A + E + 1600)) ≤
    ((min (1 / (200 * m)) ((Real.exp (-E) / 2) / (400 * m * (W + 1)))).toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hmin]
  apply le_min
  · apply (le_div_iff₀ (by positivity : 0 < 200 * m)).mpr
    have hsmall : 200 * m ≤ 800 * m * (W + 1) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)).trans
      (hscaled.trans (Real.exp_le_one_iff.mpr (by linarith)))
  · rw [div_div, show 2 * (400 * m * (W + 1)) = 800 * m * (W + 1) by ring]
    exact (le_div_iff₀ (by positivity)).mpr hscaled

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteApproximationComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem indicator_comparison_le {I lower upper a b W : ℝ}
    (hW : 0 ≤ W) (ha : 0 ≤ a) (hb : b ≤ W) (hlo : lower ≤ I) (hhi : I ≤ upper) :
    I * (a - b) ≤ upper * (a - b) + W * (upper - lower) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hhi) ha,
    mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hhi),
    mul_nonneg hW (sub_nonneg.mpr hlo)]

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem mean_indicator_comparison_le (S : Finset G) (f g lower upper : G → ℝ)
    {W epsilon gamma : ℝ} (hW : 0 ≤ W) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hsand : ∀ x, lower x ≤ (if x ∈ S then (1 : ℝ) else 0) ∧
      (if x ∈ S then (1 : ℝ) else 0) ≤ upper x)
    (hmean : (𝔼 x, upper x * (f x - g x)) ≤ epsilon)
    (hgap : (𝔼 x, (upper x - lower x)) ≤ gamma) :
    (𝔼 x, if x ∈ S then f x - g x else 0) ≤ epsilon + W * gamma := by
  calc
    _ ≤ 𝔼 x, (upper x * (f x - g x) + W * (upper x - lower x)) := by
      apply Finset.expect_le_expect
      intro x _
      have h := indicator_comparison_le hW (hf x) (hg x) (hsand x).1 (hsand x).2
      simpa only [ite_mul, one_mul, zero_mul] using h
    _ = (𝔼 x, upper x * (f x - g x)) + W * (𝔼 x, (upper x - lower x)) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ ≤ _ := add_le_add hmean (mul_le_mul_of_nonneg_left hgap hW)

theorem local_average_le_of_approximation (S : Finset G) (hS : S.Nonempty)
    (f g lower upper : G → ℝ) {W epsilon kappa : ℝ}
    (hW : 0 ≤ W) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hsand : ∀ x, lower x ≤ (if x ∈ S then (1 : ℝ) else 0) ∧
      (if x ∈ S then (1 : ℝ) else 0) ≤ upper x)
    (hmean : (𝔼 x, upper x * (f x - g x)) ≤ epsilon)
    (hgap : (𝔼 x, (upper x - lower x)) ≤ kappa * ((S.card : ℝ) / Fintype.card G)) :
    (𝔼 x ∈ S, (f x - g x)) ≤ (Fintype.card G : ℝ) / S.card * epsilon + W * kappa := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hGc : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast hS.card_pos.trans_le (Finset.card_le_univ S)
  have h := mean_indicator_comparison_le S f g lower upper hW hf hg hsand hmean hgap
  have heq : (𝔼 x, if x ∈ S then f x - g x else 0) =
      (S.card : ℝ) / Fintype.card G * (𝔼 x ∈ S, (f x - g x)) := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
    rw [← Finset.card_mul_expect S (fun x => f x - g x)]
    ring
  rw [heq] at h
  calc
    _ = ((Fintype.card G : ℝ) / S.card) *
        (((S.card : ℝ) / Fintype.card G) * (𝔼 x ∈ S, (f x - g x))) := by
      field_simp
    _ ≤ ((Fintype.card G : ℝ) / S.card) *
        (epsilon + W * (kappa * ((S.card : ℝ) / Fintype.card G))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

theorem finiteSetLp_of_pos (s : Finset ι) (f : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s f p = (𝔼 i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ)) := by
  simp only [finiteSetLp, hp.ne', ite_false]

theorem finiteSetLp_nonneg (s : Finset ι) (f : ι → ℝ) (p : ℕ) :
    0 ≤ finiteSetLp s f p := by
  unfold finiteSetLp
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (Finset.expect_nonneg (fun _ _ => by positivity)) _

theorem finiteSetLp_pow (s : Finset ι) (f : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s f p ^ p = 𝔼 i ∈ s, |f i| ^ p := by
  rw [finiteSetLp_of_pos s f hp, ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.expect_nonneg (fun _ _ => by positivity))]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [one_div_mul_cancel hpR, Real.rpow_one]

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

theorem expect_tail_mul_pow_le (S : Finset ι) (f : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (q : ℕ) :
    t ^ q * (𝔼 i ∈ S, if t < |f i| then (1 : ℝ) else 0) ≤ 𝔼 i ∈ S, |f i| ^ q := by
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro i _
  by_cases hi : t < |f i|
  · simpa only [hi, ite_true, mul_one] using pow_le_pow_left₀ ht hi.le q
  · simp only [hi, ite_false, mul_zero]
    positivity

theorem finiteSetLp_tail_le (S : Finset ι) (f : ι → ℝ) {q : ℕ} (hq : 0 < q)
    {delta t : ℝ} (ht : 0 < t) (hLp : finiteSetLp S f q ≤ delta) :
    (𝔼 i ∈ S, if t < |f i| then (1 : ℝ) else 0) ≤ (delta / t) ^ q := by
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos ht q)).mpr
  calc
    _ = t ^ q * (𝔼 i ∈ S, if t < |f i| then (1 : ℝ) else 0) := mul_comm _ _
    _ ≤ 𝔼 i ∈ S, |f i| ^ q := expect_tail_mul_pow_le S f ht.le q
    _ = finiteSetLp S f q ^ q := (finiteSetLp_pow S f hq).symm
    _ ≤ delta ^ q := pow_le_pow_left₀ (finiteSetLp_nonneg S f q) hLp q

theorem finiteSetLp_double_tail_le (S : Finset ι) (f : ι → ℝ) {q : ℕ} (hq : 0 < q)
    {delta : ℝ} (hdelta : 0 < delta) (hLp : finiteSetLp S f q ≤ delta) :
    (𝔼 i ∈ S, if 2 * delta < |f i| then (1 : ℝ) else 0) ≤ (1 / 2 : ℝ) ^ q := by
  have h := finiteSetLp_tail_le S f hq (show 0 < 2 * delta by positivity) hLp
  have heq : delta / (2 * delta) = (1 / 2 : ℝ) := by field_simp
  simpa only [heq] using h

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

end Erdos3.LocalConvolution

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

theorem flat_weighted_pointwise_le {A B d epsilon delta W M : ℝ}
    (hA : 0 ≤ A ∧ A ≤ W) (hB : 0 ≤ B ∧ B ≤ W) (hd : 0 ≤ d ∧ d ≤ M)
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta)) :
    (A - (1 + epsilon) * B) * d ≤ (1 + 2 * delta) * (A - B) +
      W * (M + 2) * (if 2 * delta < |d - 1| then (1 : ℝ) else 0) := by
  by_cases hbad : 2 * delta < |d - 1|
  · simp only [hbad, ite_true, mul_one]
    have hW : 0 ≤ W := hA.1.trans hA.2
    have hAd : A * d ≤ W * M := mul_le_mul hA.2 hd.2 hd.1 hW
    have hBweight : (1 + 2 * delta) * B ≤ 2 * W :=
      mul_le_mul (by linarith) hB.2 hB.1 (by norm_num)
    have hAnonneg : 0 ≤ (1 + 2 * delta) * A := mul_nonneg (by linarith) hA.1
    have hnegative : 0 ≤ ((1 + epsilon) * B) * d :=
      mul_nonneg (mul_nonneg (by linarith) hB.1) hd.1
    nlinarith
  · simp only [hbad, ite_false, mul_zero, add_zero]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (le_of_not_gt hbad)
    have hAd : A * d ≤ A * (1 + 2 * delta) := mul_le_mul_of_nonneg_left (by linarith) hA.1
    have hBd : (1 + epsilon) * B * (1 - 2 * delta) ≤ (1 + epsilon) * B * d :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hB.1)
    have hBcoeff := mul_le_mul_of_nonneg_right hcoeff hB.1
    nlinarith

theorem flat_weighted_average_le {ι : Type*} (S : Finset ι) (A B d : ι → ℝ)
    {q : ℕ} (hq : 0 < q) {epsilon delta W M eta : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hA : ∀ i ∈ S, 0 ≤ A i ∧ A i ≤ W) (hB : ∀ i ∈ S, 0 ≤ B i ∧ B i ≤ W)
    (hd : ∀ i ∈ S, 0 ≤ d i ∧ d i ≤ M)
    (hLp : finiteSetLp S (fun i => d i - 1) q ≤ delta)
    (hmean : (𝔼 i ∈ S, (A i - B i)) ≤ eta) :
    (𝔼 i ∈ S, (A i - (1 + epsilon) * B i) * d i) ≤
      (1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q := by
  have htail := finiteSetLp_double_tail_le S (fun i => d i - 1) hq hdelta hLp
  calc
    _ ≤ 𝔼 i ∈ S, ((1 + 2 * delta) * (A i - B i) +
        W * (M + 2) * (if 2 * delta < |d i - 1| then (1 : ℝ) else 0)) := by
      apply Finset.expect_le_expect
      intro i hi
      exact flat_weighted_pointwise_le (hA i hi) (hB i hi) (hd i hi)
        hepsilon hdelta.le hdelta2 hcoeff
    _ = (1 + 2 * delta) * (𝔼 i ∈ S, (A i - B i)) +
        W * (M + 2) * (𝔼 i ∈ S, if 2 * delta < |d i - 1| then (1 : ℝ) else 0) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hmean (by positivity))
      (mul_le_mul_of_nonneg_left htail (by positivity))

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI

namespace Erdos3

open scoped BigOperators

end Erdos3

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem expect_eq_total_div (B : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) : (𝔼 x ∈ B, f x) = (∑ x, f x) / B.card := by
  rw [Finset.expect_eq_sum_div_card]
  congr 1
  exact Finset.sum_subset (Finset.subset_univ B) (fun x _ hx => hf x hx)

end Erdos3.Peeling

namespace Erdos3

open scoped BigOperators

namespace Peeling

end Peeling

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end CellRefinement
end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem convolution_nonneg (L : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (t : G) :
    0 ≤ convolution L f g t :=
  div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hf x) (hg (t - x)))) (Nat.cast_nonneg _)

theorem convolution_le_of_mass (L : Finset G) (f g : G → ℝ) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ M)
    (hmass : (∑ x, f x) / (L.card : ℝ) = 1) (t : G) : convolution L f g t ≤ M := by
  unfold convolution
  calc
    _ ≤ (∑ x, f x * M) / (L.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hg (t - x)) (hf x))
    _ = ((∑ x, f x) / (L.card : ℝ)) * M := by rw [← Finset.sum_mul]; ring
    _ = M := by rw [hmass, one_mul]

omit [AddCommGroup G] in
theorem normalized_mass_one (L : Finset G) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) {u : ℝ} (hu : 0 < u)
    (hmean : (𝔼 x ∈ L, f x) = u) : (∑ x, f x / u) / (L.card : ℝ) = 1 := by
  have hmass : (∑ x, f x) / (L.card : ℝ) = u := by
    rw [← Peeling.expect_eq_total_div L f hsupport]
    exact hmean
  rw [← Finset.sum_div]
  calc
    _ = ((∑ x, f x) / (L.card : ℝ)) / u := by ring
    _ = 1 := by rw [hmass, div_self hu.ne']

end Erdos3.LocalConvolution

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

end Chain
end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

theorem matchedIntegral_sum_order (L S : Finset G) (a f g : G → ℝ) :
    matchedIntegral L S a f g =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 r ∈ L, f r * g (-r + (s + t)) * a (s + t) := by
  unfold matchedIntegral matchedPairAverage
  rw [Finset.expect_comm L S]
  apply Finset.expect_congr rfl
  intro s _
  rw [Finset.expect_comm L S]
  apply Finset.expect_congr rfl
  intro t _
  apply Finset.expect_congr rfl
  intro r _
  dsimp only
  have heq : r + (-r + s + t) = s + t := by abel
  rw [heq, add_assoc (-r) s t]

theorem matchedIntegral_div_weights (L S : Finset G) (a f g : G → ℝ) (u v : ℝ) :
    matchedIntegral L S a (fun x => f x / u) (fun y => g y / v) =
      matchedIntegral L S a f g / (u * v) := by
  simp only [matchedIntegral_sum_order]
  have heq (r s t : G) : f r / u * (g (-r + (s + t)) / v) * a (s + t) =
      (f r * g (-r + (s + t)) * a (s + t)) / (u * v) := by ring
  simp_rw [heq, ← Finset.expect_div]

variable [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem matchedIntegral_eq_convolution (L S : Finset G) (a f g : G → ℝ)
    (hfsupport : ∀ x, x ∉ L → f x = 0) :
    matchedIntegral L S a f g =
      𝔼 s ∈ S, 𝔼 t ∈ S, a (s + t) * LocalConvolution.convolution L f g (s + t) := by
  rw [matchedIntegral_sum_order]
  apply Finset.expect_congr rfl
  intro s _
  apply Finset.expect_congr rfl
  intro t _
  have heq (r : G) : -r + (s + t) = (s + t) - r := by abel
  simp_rw [heq]
  rw [← Finset.expect_mul, Peeling.expect_eq_total_div L (fun r => f r * g ((s + t) - r))]
  · unfold LocalConvolution.convolution
    ring
  · intro r hr
    rw [hfsupport r hr, zero_mul]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem matched_flat_integral_le (L S : Finset G) (A B f g : G → ℝ)
    {q : ℕ} (hq : 0 < q) {epsilon delta W M eta : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ W) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmass : (∑ x, f x) / (L.card : ℝ) = 1)
    (hflat : LocalConvolution.sumLp S (fun x => LocalConvolution.convolution L f g x - 1) q ≤ delta)
    (hmean : (𝔼 s ∈ S, 𝔼 t ∈ S, (A (s + t) - B (s + t))) ≤ eta) :
    matchedIntegral L S (fun x => A x - (1 + epsilon) * B x) f g ≤
      (1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q := by
  have h := flat_weighted_average_le (S ×ˢ S)
    (fun z => A (z.1 + z.2)) (fun z => B (z.1 + z.2))
    (fun z => LocalConvolution.convolution L f g (z.1 + z.2)) hq
    hW hM hepsilon hdelta hdelta2 hcoeff (fun z _ => hA _) (fun z _ => hB _)
    (fun z _ => ⟨LocalConvolution.convolution_nonneg L f g hf (fun x => (hg x).1) _,
      LocalConvolution.convolution_le_of_mass L f g hf (fun x => (hg x).2) hfmass _⟩)
    hflat (by simpa only [Finset.expect_product] using hmean)
  rw [matchedIntegral_eq_convolution L S _ f g hfsupport]
  simpa only [Finset.expect_product] using h

theorem matched_flat_integral_le_normalized (L S : Finset G) (A B f g : G → ℝ)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) {q : ℕ} (hq : 0 < q)
    {epsilon delta W M eta : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ W) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤ delta)
    (hmean : (𝔼 s ∈ S, 𝔼 t ∈ S, (A (s + t) - B (s + t))) ≤ eta) :
    matchedIntegral L S (fun x => A x - (1 + epsilon) * B x) f g ≤
      (u * v) * ((1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q) := by
  have hnorm := LocalConvolution.normalized_mass_one L f hfsupport hu hfmean
  have h := matched_flat_integral_le L S A B (fun x => f x / u) (fun x => g x / v)
    hq hW hM hepsilon hdelta hdelta2 hcoeff hA hB
    (fun x => div_nonneg (hf x) hu.le) (fun x => ⟨div_nonneg (hg x) hv.le, hgcap x⟩)
    (fun x hx => by rw [hfsupport x hx, zero_div]) hnorm hflat hmean
  rw [matchedIntegral_div_weights] at h
  simpa only [mul_comm] using (div_le_iff₀ (mul_pos hu hv)).mp h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {I : Type*}

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MatchedFlatDecay
namespace OAI

section

namespace Erdos3

theorem flatComparisonDelta_spec {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < flatComparisonDelta epsilon ∧ flatComparisonDelta epsilon ≤ 1 / 4 ∧
      1 + 2 * flatComparisonDelta epsilon ≤
        (1 + epsilon) * (1 - 2 * flatComparisonDelta epsilon) := by
  have hden : 0 < 4 * (2 + epsilon) := by positivity
  have hprod : flatComparisonDelta epsilon * (4 * (2 + epsilon)) = epsilon :=
    div_mul_cancel₀ _ hden.ne'
  refine ⟨div_pos hepsilon hden, ?_, ?_⟩
  · unfold flatComparisonDelta
    apply (div_le_iff₀ hden).mpr
    linarith
  · nlinarith

theorem exp_mul_half_pow_le {a b : ℝ} (q : ℕ)
    (hq : a + b ≤ (q : ℝ) * Real.log 2) :
    Real.exp a * (1 / 2 : ℝ) ^ q ≤ Real.exp (-b) := by
  have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hhalf, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem flat_exception_error_le {A B D p W M : ℝ}
    (hp : 1 ≤ p) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hWcap : W ≤ Real.exp (A * p)) (hMcap : M ≤ Real.exp (B * p))
    (q : ℕ) (hq : (A + B + D + Real.log 3) * p ≤ (q : ℝ) * Real.log 2) :
    W * (M + 2) * (1 / 2 : ℝ) ^ q ≤ Real.exp (-(D * p)) := by
  have hp0 : 0 ≤ p := by linarith
  have hone : 1 ≤ Real.exp (B * p) := Real.one_le_exp_iff.mpr (mul_nonneg hB hp0)
  have hMtwo : M + 2 ≤ 3 * Real.exp (B * p) := by linarith
  have hproduct : W * (M + 2) ≤ 3 * Real.exp ((A + B) * p) := by
    calc
      _ ≤ Real.exp (A * p) * (3 * Real.exp (B * p)) :=
        mul_le_mul hWcap hMtwo (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [add_mul, Real.exp_add]; ring
  have hlog3 : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).le
  have hthreshold : Real.log 3 + (A + B) * p + D * p ≤ (q : ℝ) * Real.log 2 := by
    have hlog := mul_le_mul_of_nonneg_left hp hlog3
    nlinarith
  calc
    _ ≤ (3 * Real.exp ((A + B) * p)) * (1 / 2 : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right hproduct (by positivity)
    _ = Real.exp (Real.log 3 + (A + B) * p) * (1 / 2 : ℝ) ^ q := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := exp_mul_half_pow_le q hthreshold

end Erdos3

end

section

namespace Erdos3

theorem exp_extra_decay_le_half {D p : ℝ} (hp : 1 ≤ p) :
    Real.exp (-((D + 1) * p)) ≤ Real.exp (-(D * p)) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  calc
    _ = Real.exp (-(D * p)) / Real.exp p := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) htwo

theorem flat_total_error_le_exp {A B D p W M delta eta : ℝ}
    (hp : 1 ≤ p) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hWcap : W ≤ Real.exp (A * p)) (hMcap : M ≤ Real.exp (B * p))
    (hdelta : 0 ≤ delta) (hdelta2 : delta ≤ 1 / 2)
    (heta : eta ≤ Real.exp (-(D * p)) / 4)
    (q : ℕ) (hq : (A + B + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2) :
    (1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q ≤ Real.exp (-(D * p)) := by
  have hexception := (flat_exception_error_le hp hB hM hWcap hMcap q hq).trans
    (exp_extra_decay_le_half (D := D) hp)
  have hmean := mul_le_mul_of_nonneg_left heta (show 0 ≤ 1 + 2 * delta by positivity)
  have hsmall := mul_le_mul_of_nonneg_right hdelta2 (Real.exp_nonneg (-(D * p)))
  nlinarith

end Erdos3

end

section

namespace Erdos3.LocalConvolution

end Erdos3.LocalConvolution

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem matched_flat_integral_decay
    (L S : Finset G) (A B f g : G → ℝ) {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hu1 : u ≤ 1) (hv1 : v ≤ 1) {q : ℕ} (hq : 0 < q)
    {epsilon delta W M eta a b D p : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hp : 1 ≤ p) (hb : 0 ≤ b) (hWcap : W ≤ Real.exp (a * p)) (hMcap : M ≤ Real.exp (b * p))
    (heta : eta ≤ Real.exp (-(D * p)) / 4)
    (horder : (a + b + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ W) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤ delta)
    (hmean : (𝔼 s ∈ S, 𝔼 t ∈ S, (A (s + t) - B (s + t))) ≤ eta) :
    matchedIntegral L S (fun x => A x - (1 + epsilon) * B x) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hbase := matched_flat_integral_le_normalized L S A B f g hu hv hq hW hM hepsilon
    hdelta hdelta2 hcoeff hA hB hf hg hgcap hfsupport hfmean hflat hmean
  have herr := flat_total_error_le_exp hp hb hM hWcap hMcap hdelta.le hdelta2 heta q horder
  have hroot : u * v ≤ (u * v) ^ (1 / 4 : ℝ) :=
    Real.self_le_rpow_of_le_one (mul_nonneg hu.le hv.le)
      ((mul_le_mul hu1 hv1 hv.le (by norm_num)).trans_eq (one_mul 1)) (by norm_num)
  calc
    _ ≤ (u * v) * Real.exp (-(D * p)) :=
      hbase.trans (mul_le_mul_of_nonneg_left herr (mul_nonneg hu.le hv.le))
    _ ≤ (u * v) ^ (1 / 4 : ℝ) * Real.exp (-(D * p)) :=
      mul_le_mul_of_nonneg_right hroot (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExponentialBohrVolume
namespace OAI

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

namespace Set

end Set
end CyclicBohr
end Erdos3

end

section

namespace Erdos3

open AddChar _root_.Finset
open scoped BigOperators

namespace CyclicBohr

variable {N : ℕ} [NeZero N]

lemma scaledArg_nonneg (m : ℕ) (z : ℂ) : 0 ≤ scaledArg m z := by
  unfold scaledArg
  have hz : 0 ≤ z.arg + Real.pi := by linarith [Complex.neg_pi_lt_arg z]
  positivity

lemma abs_scaledArg_sub_lt_one_of_argBin_eq {m : ℕ} {z w : ℂ}
    (hbin : argBin m z = argBin m w) :
    |scaledArg m z - scaledArg m w| < 1 := by
  have hfloor : ⌊scaledArg m z⌋₊ = ⌊scaledArg m w⌋₊ :=
    congrArg Fin.val hbin
  have hfloorR : (⌊scaledArg m z⌋₊ : ℝ) = ⌊scaledArg m w⌋₊ := by
    exact_mod_cast hfloor
  have hzlow : (⌊scaledArg m z⌋₊ : ℝ) ≤ scaledArg m z :=
    Nat.floor_le (scaledArg_nonneg m z)
  have hwlow : (⌊scaledArg m w⌋₊ : ℝ) ≤ scaledArg m w :=
    Nat.floor_le (scaledArg_nonneg m w)
  have hzup : scaledArg m z < (⌊scaledArg m z⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hwup : scaledArg m w < (⌊scaledArg m w⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [abs_lt]
  constructor <;> nlinarith

lemma abs_arg_sub_lt_of_argBin_eq {m : ℕ} (hm : 0 < m) {z w : ℂ}
    (hbin : argBin m z = argBin m w) :
    |z.arg - w.arg| < 2 * Real.pi / m := by
  have h := abs_scaledArg_sub_lt_one_of_argBin_eq hbin
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : 0 < 2 * Real.pi := by positivity
  have hscale :
      |scaledArg m z - scaledArg m w| =
        |z.arg - w.arg| * (m : ℝ) / (2 * Real.pi) := by
    have heq : scaledArg m z - scaledArg m w =
        (z.arg - w.arg) * (m : ℝ) / (2 * Real.pi) := by
      unfold scaledArg
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hmR, abs_of_pos hpi]
  rw [hscale] at h
  rw [lt_div_iff₀ hmR]
  exact (div_lt_one hpi).mp h

lemma sub_mem_of_argumentCode_eq (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) {x y : ZMod N}
    (hcode : argumentCode B m x = argumentCode B m y) :
    x - y ∈ B := by
  rw [Set.mem_iff]
  intro r hr
  have hbin : argBin m (character r x) = argBin m (character r y) := by
    exact congrFun hcode ⟨r, hr⟩
  calc
    ‖1 - character r (x - y)‖ = ‖character r x - character r y‖ :=
      norm_one_sub_character_sub r x y
    _ ≤ |(character r x).arg - (character r y).arg| :=
      norm_sub_le_abs_arg_sub_of_norm_eq_one (norm_character r x) (norm_character r y)
    _ ≤ 2 * Real.pi / m := (abs_arg_sub_lt_of_argBin_eq hm hbin).le
    _ ≤ B.radius := hwidth

end CyclicBohr
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

open _root_.Finset
open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem card_le_codeCard_mul_card (B : Set N) {m : ℕ} (hm : 0 < m)
    (hwidth : 2 * Real.pi / m ≤ B.radius) :
    N ≤ (m + 1) ^ B.rank * B.carrier.card := by
  classical
  let Q := (r : ↥B.frequencies) → Fin (m + 1)
  let code : ZMod N → Q := argumentCode B m
  have hQ : Fintype.card Q = (m + 1) ^ B.rank := card_argumentCodeSpace B m
  by_contra h
  have hsmall : Fintype.card Q * B.carrier.card < Fintype.card (ZMod N) := by
    simpa only [hQ, ZMod.card] using (not_le.mp h)
  obtain ⟨q, hq⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := code) hsmall
  let A := Finset.univ.filter (fun x : ZMod N => code x = q)
  have hA : B.carrier.card < A.card := by simpa only [A] using hq
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp ((Nat.zero_le _).trans_lt hA)
  let e : ZMod N ↪ ZMod N := (Equiv.subRight x₀).toEmbedding
  have hmap : A.map e ⊆ B.carrier := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    exact sub_mem_of_argumentCode_eq B hm hwidth
      ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hx₀).2.symm)
  have hcard := Finset.card_le_card hmap
  rw [Finset.card_map] at hcard
  omega

theorem card_lower_bound (B : Set N) (hB : 0 < B.radius) (hB1 : B.radius ≤ 1) :
    (B.radius / 10) ^ B.rank * N ≤ (B.carrier.card : ℝ) := by
  let m := ⌈2 * Real.pi / B.radius⌉₊
  have hratio : 0 < 2 * Real.pi / B.radius := div_pos (by positivity) hB
  have hm : 0 < m := Nat.ceil_pos.mpr hratio
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwidth : 2 * Real.pi / m ≤ B.radius := by
    rw [div_le_iff₀ hmR]
    have h := (div_le_iff₀ hB).mp (Nat.le_ceil (2 * Real.pi / B.radius))
    nlinarith
  have hcode : (N : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ B.rank * B.carrier.card := by
    exact_mod_cast card_le_codeCard_mul_card B hm hwidth
  have hmUpper : ((m + 1 : ℕ) : ℝ) ≤ 10 / B.radius := by
    have hceil := Nat.ceil_lt_add_one hratio.le
    rw [Nat.cast_add, Nat.cast_one]
    change (⌈2 * Real.pi / B.radius⌉₊ : ℝ) + 1 ≤ _
    rw [le_div_iff₀ hB]
    have hceilmul := mul_lt_mul_of_pos_right hceil hB
    have hquot : (2 * Real.pi / B.radius) * B.radius = 2 * Real.pi :=
      div_mul_cancel₀ _ hB.ne'
    nlinarith [Real.pi_lt_four]
  have hpower : ((B.radius / 10) * ((m + 1 : ℕ) : ℝ)) ^ B.rank ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hmUpper (show 0 ≤ B.radius / 10 by positivity)
    have heq : B.radius / 10 * (10 / B.radius) = 1 := by field_simp
    exact hmul.trans_eq heq
  calc
    _ ≤ (B.radius / 10) ^ B.rank * (((m + 1 : ℕ) : ℝ) ^ B.rank * B.carrier.card) :=
      mul_le_mul_of_nonneg_left hcode (by positivity)
    _ = ((B.radius / 10) * ((m + 1 : ℕ) : ℝ)) ^ B.rank * B.carrier.card := by
      rw [mul_pow]
      ring
    _ ≤ 1 * (B.carrier.card : ℝ) := mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg _)
    _ = _ := one_mul _

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr

end

section

namespace Erdos3.CyclicBohr.Set

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CyclicAffineCharacterPhase
namespace OAI

section

namespace Erdos3.CircleFourier

theorem character_sub (x y : Circle) : character (x - y) = character x / character y := by
  have hne : character y ≠ 0 := by
    intro h
    have hn := norm_character y
    rw [h, norm_zero] at hn
    norm_num at hn
  apply (eq_div_iff hne).mpr
  rw [← character_add, sub_add_cancel]

end Erdos3.CircleFourier

namespace Erdos3.CyclicBohr

variable {N : ℕ} [NeZero N]

theorem real_frequency_phase_sub {r : ZMod N} {theta : ℝ}
    (htheta : ∀ x : ZMod N,
      CircleFourier.character (((x.val : ℝ) * theta : ℝ) : CircleFourier.Circle) = character r x)
    (x z : ZMod N) :
    CircleFourier.character ((((x.val : ℝ) - (z.val : ℝ)) * theta : ℝ) : CircleFourier.Circle) =
      character r (x - z) := by
  rw [sub_mul, AddCircle.coe_sub, CircleFourier.character_sub, htheta, htheta,
    AddChar.map_sub_eq_div]

theorem exists_real_frequency_phases (B : Set N) :
    ∃ theta : B.frequencies → ℝ, ∀ x z : ZMod N, ∀ r : B.frequencies,
      CircleFourier.character ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle) =
        character r (x - z) := by
  classical
  choose theta htheta using (fun r : B.frequencies => exists_real_frequency_phase (r : ZMod N))
  exact ⟨theta, fun x z r => real_frequency_phase_sub (htheta r) x z⟩

end Erdos3.CyclicBohr

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChordBoxCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem chordBoxCutoff_range (a : ℝ) (h : ℝ≥0) (z : ι → ℂ) :
    0 ≤ chordBoxCutoff a h z ∧ chordBoxCutoff a h z ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (linearCutoff_range a h _).1),
    Finset.prod_le_one (fun i _ => (linearCutoff_range a h _).1)
      (fun i _ => (linearCutoff_range a h _).2)⟩

theorem chordBoxCutoff_eq_one (a : ℝ) (h : ℝ≥0) (hh : 0 < h)
    (z : ι → ℂ) (hz : ∀ i, ‖1 - z i‖ ≤ a) : chordBoxCutoff a h z = 1 := by
  exact Finset.prod_eq_one (fun i _ => linearCutoff_eq_one a h hh (hz i))

theorem chordBoxCutoff_eq_zero (a : ℝ) (h : ℝ≥0) (z : ι → ℂ)
    (hz : ∃ i, a + (h : ℝ) ≤ ‖1 - z i‖) : chordBoxCutoff a h z = 0 := by
  classical
  obtain ⟨i, hi⟩ := hz
  exact Finset.prod_eq_zero (Finset.mem_univ i) (linearCutoff_eq_zero a h hi)

theorem chordBoxCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith (Fintype.card ι * h⁻¹) (chordBoxCutoff (ι := ι) a h) := by
  have hsingle : LipschitzWith h⁻¹ (fun z : ℂ => linearCutoff a h ‖1 - z‖) := by
    simpa only [Function.comp_def, mul_one, dist_eq_norm] using
      (linearCutoff_lipschitz a h hh).comp (LipschitzWith.dist_right (1 : ℂ))
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hcoord (i : ι) :
      |linearCutoff a h ‖1 - z i‖ - linearCutoff a h ‖1 - w i‖| ≤
        (h⁻¹ : ℝ≥0) * dist z w := by
    have hi := hsingle.dist_le_mul (z i) (w i)
    rw [Real.dist_eq] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist z w i) (by positivity))
  have hprod := abs_finset_prod_sub_prod_le Finset.univ
    (fun i => linearCutoff a h ‖1 - z i‖) (fun i => linearCutoff a h ‖1 - w i‖)
    (B := 1) (δ := (h⁻¹ : ℝ≥0) * dist z w) le_rfl (by positivity)
    (fun i _ => by rw [abs_of_nonneg (linearCutoff_range a h _).1]; exact (linearCutoff_range a h _).2)
    (fun i _ => by rw [abs_of_nonneg (linearCutoff_range a h _).1]; exact (linearCutoff_range a h _).2)
    (fun i _ => hcoord i)
  rw [Real.dist_eq]
  apply hprod.trans_eq
  simp only [Finset.card_univ, one_pow, mul_one, NNReal.coe_mul, NNReal.coe_natCast]
  ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem torusChordCutoff_range (a : ℝ) (h : ℝ≥0) (v : ι → CircleFourier.Circle) :
    0 ≤ torusChordCutoff a h v ∧ torusChordCutoff a h v ≤ 1 := chordBoxCutoff_range _ _ _

theorem torus_character_map_lipschitz :
    LipschitzWith CircleFourier.characterLipConstant
      (fun v : ι → CircleFourier.Circle => fun i => CircleFourier.character (v i)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [dist_eq_norm]
  change ‖(fun i => CircleFourier.character (v i)) - (fun i => CircleFourier.character (w i))‖ ≤
    (2 * Real.pi) * dist v w
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖CircleFourier.character (v i) - CircleFourier.character (w i)‖ ≤ _
  have h : ‖CircleFourier.character (v i) - CircleFourier.character (w i)‖ ≤
      (2 * Real.pi) * dist (v i) (w i) := by
    simpa only [dist_eq_norm, CircleFourier.coe_characterLipConstant] using
      CircleFourier.character_lipschitz.dist_le_mul (v i) (w i)
  exact h.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist v w i)
    (show 0 ≤ 2 * Real.pi by positivity))

theorem torusChordCutoff_lipschitz (a : ℝ) (h : ℝ≥0) (hh : 0 < h) :
    LipschitzWith (((Fintype.card ι : ℝ≥0) * h⁻¹) * CircleFourier.characterLipConstant)
      (torusChordCutoff (ι := ι) a h) :=
  (chordBoxCutoff_lipschitz a h hh).comp torus_character_map_lipschitz

end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem approximationWidth_pos (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho) :
    0 < B.approximationWidth rho := mul_pos hrho hB

theorem upperApprox_range (B : Set N) (rho : ℝ≥0) (x : ZMod N) :
    0 ≤ B.upperApprox rho x ∧ B.upperApprox rho x ≤ 1 := chordBoxCutoff_range _ _ _

theorem lowerApprox_range (B : Set N) (rho : ℝ≥0) (x : ZMod N) :
    0 ≤ B.lowerApprox rho x ∧ B.lowerApprox rho x ≤ 1 := chordBoxCutoff_range _ _ _

theorem upperApprox_eq_one (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho)
    {x : ZMod N} (hx : x ∈ B.carrier) : B.upperApprox rho x = 1 := by
  apply chordBoxCutoff_eq_one _ _ (B.approximationWidth_pos hB rho hrho)
  intro r
  exact (mem_carrier.mp hx) r r.property

theorem lowerApprox_eq_zero (B : Set N) (rho : ℝ≥0) {x : ZMod N} (hx : x ∉ B.carrier) :
    B.lowerApprox rho x = 0 := by
  rw [mem_carrier] at hx
  push Not at hx
  obtain ⟨r, hr, hbad⟩ := hx
  apply chordBoxCutoff_eq_zero
  refine ⟨⟨r, hr⟩, ?_⟩
  change B.radius - (rho : ℝ) * B.radius + (rho : ℝ) * B.radius ≤ ‖1 - character r x‖
  linarith

theorem lowerApprox_eq_one_inner (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) {x : ZMod N} (hx : x ∈ (B.ndilate (1 - rho)).carrier) :
    B.lowerApprox rho x = 1 := by
  apply chordBoxCutoff_eq_one _ _ (B.approximationWidth_pos hB rho hrho)
  intro r
  have h := (mem_carrier.mp hx) r r.property
  rw [radius_ndilate, NNReal.coe_sub hrho1, NNReal.coe_one] at h
  change ‖1 - character r x‖ ≤ B.radius - (rho : ℝ) * B.radius
  nlinarith

theorem upperApprox_eq_zero_outer (B : Set N) (rho : ℝ≥0) {x : ZMod N}
    (hx : x ∉ (B.ndilate (1 + rho)).carrier) : B.upperApprox rho x = 0 := by
  rw [mem_carrier] at hx
  push Not at hx
  obtain ⟨r, hr, hbad⟩ := hx
  apply chordBoxCutoff_eq_zero
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [radius_ndilate, NNReal.coe_add, NNReal.coe_one] at hbad
  change B.radius + (rho : ℝ) * B.radius ≤ ‖1 - character r x‖
  nlinarith

theorem approximation_sandwich (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho)
    (x : ZMod N) :
    B.lowerApprox rho x ≤ (if x ∈ B.carrier then (1 : ℝ) else 0) ∧
      (if x ∈ B.carrier then (1 : ℝ) else 0) ≤ B.upperApprox rho x := by
  by_cases hx : x ∈ B.carrier
  · simp only [hx, ite_true]
    exact ⟨(B.lowerApprox_range rho x).2, (B.upperApprox_eq_one hB rho hrho hx).ge⟩
  · simp only [hx, ite_false]
    exact ⟨(B.lowerApprox_eq_zero rho hx).le, (B.upperApprox_range rho x).1⟩

theorem approximation_gap_le_shell (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (x : ZMod N) :
    B.upperApprox rho x - B.lowerApprox rho x ≤
      (if x ∈ (B.ndilate (1 + rho)).carrier then (1 : ℝ) else 0) -
        (if x ∈ (B.ndilate (1 - rho)).carrier then (1 : ℝ) else 0) := by
  by_cases hi : x ∈ (B.ndilate (1 - rho)).carrier
  · have ho : x ∈ (B.ndilate (1 + rho)).carrier :=
      carrier_ndilate_mono ((tsub_le_self : 1 - rho ≤ (1 : ℝ≥0)).trans le_self_add) hi
    simp only [hi, ho, ite_true]
    rw [B.lowerApprox_eq_one_inner hB rho hrho hrho1 hi]
    linarith [(B.upperApprox_range rho x).2]
  · simp only [hi, ite_false, sub_zero]
    by_cases ho : x ∈ (B.ndilate (1 + rho)).carrier
    · simp only [ho, ite_true]
      linarith [(B.upperApprox_range rho x).2, (B.lowerApprox_range rho x).1]
    · simp only [ho, ite_false]
      rw [B.upperApprox_eq_zero_outer rho ho]
      linarith [(B.lowerApprox_range rho x).1]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem sum_approximation_gap_le (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (∑ x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * B.carrier.card := by
  have hrho1 : rho ≤ 1 := by
    apply hsmall.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have hsum : (∑ x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      ((B.ndilate (1 + rho)).carrier.card : ℝ) - (B.ndilate (1 - rho)).carrier.card := by
    calc
      _ ≤ ∑ x, ((if x ∈ (B.ndilate (1 + rho)).carrier then (1 : ℝ) else 0) -
          (if x ∈ (B.ndilate (1 - rho)).carrier then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun x _ => B.approximation_gap_le_shell hBpos rho hrho hrho1 x)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcards := hB rho hsmall
  push_cast at hcards ⊢
  nlinarith [hcards.1, hcards.2]

theorem mean_approximation_gap_le (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (𝔼 x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) * ((B.carrier.card : ℝ) / N) := by
  rw [Fintype.expect_eq_sum_div_card]
  have h := div_le_div_of_nonneg_right (B.sum_approximation_gap_le hBpos hB rho hrho hsmall)
    (Nat.cast_nonneg (Fintype.card (ZMod N)) : (0 : ℝ) ≤ Fintype.card (ZMod N))
  simpa only [ZMod.card, mul_div_assoc] using h

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem average_sub_le_of_upperApprox
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) {W epsilon : ℝ} (hW : 0 ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W) (z : ZMod N)
    (hcompare : (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon) :
    (𝔼 x ∈ B.carrier, (f (z + x) - g (z + x))) ≤
      (N : ℝ) / B.carrier.card * epsilon + W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) := by
  have hmean : (𝔼 x, B.upperApprox rho x * (f (z + x) - g (z + x))) ≤ epsilon := by
    calc
      _ = 𝔼 x, B.upperApprox rho (x - z) * (f x - g x) := by
        apply Fintype.expect_equiv (Equiv.addLeft z)
        intro x
        simp
      _ ≤ epsilon := hcompare
  have hgap : (𝔼 x, (B.upperApprox rho x - B.lowerApprox rho x)) ≤
      (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) *
        ((B.carrier.card : ℝ) / Fintype.card (ZMod N)) := by
    simpa only [ZMod.card] using B.mean_approximation_gap_le hBpos hB rho hrho hsmall
  have h := local_average_le_of_approximation B.carrier B.carrier_nonempty
    (fun x => f (z + x)) (fun x => g (z + x)) (B.lowerApprox rho) (B.upperApprox rho)
    hW (fun x => hf (z + x)) (fun x => hg (z + x))
    (B.approximation_sandwich hBpos rho hrho) hmean hgap
  simpa only [ZMod.card] using h

theorem sum_average_sub_le_of_upperApprox
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular) (rho : ℝ≥0) (hrho : 0 < rho)
    (hsmall : rho ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ) {W epsilon : ℝ} (hW : 0 ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hcompare : ∀ z, (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon)
    (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤
      (N : ℝ) / B.carrier.card * epsilon + W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) := by
  have h := Finset.expect_le_expect (fun s (_ : s ∈ B.carrier) =>
    B.average_sub_le_of_upperApprox hBpos hB rho hrho hsmall f g hW hf hg (z + s) (hcompare (z + s)))
  simpa only [Finset.expect_const B.carrier_nonempty] using h

theorem small_sum_average_of_upperApprox
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (f g : ZMod N → ℝ) {W eta epsilon : ℝ} (hW : 0 ≤ W) (heta : 0 < eta)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hepsilon : epsilon ≤ (eta / 2) * ((B.carrier.card : ℝ) / N)) :
    let rho := localizedAverageScale B.rank W (eta / 2)
    (∀ z, (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon) →
      ∀ z, (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ eta := by
  intro rho hcompare z
  obtain ⟨hrho, hsmall, herror⟩ := localizedAverageScale_spec B.rank hW
    (show 0 < eta / 2 by positivity)
  change 0 < rho at hrho
  change rho ≤ _ at hsmall
  change W * (400 * (max B.rank 1 : ℕ) * (rho : ℝ)) ≤ eta / 2 at herror
  have h := B.sum_average_sub_le_of_upperApprox hBpos hB rho hrho hsmall f g hW hf hg hcompare z
  have hcard : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have heps : (N : ℝ) / B.carrier.card * epsilon ≤ eta / 2 := by
    calc
      _ ≤ (N : ℝ) / B.carrier.card * ((eta / 2) * ((B.carrier.card : ℝ) / N)) :=
        mul_le_mul_of_nonneg_left hepsilon (by positivity)
      _ = eta / 2 := by field_simp
  linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem torus_approximation_ranges (B : Set N) (rho : ℝ≥0) (v : B.frequencies → CircleFourier.Circle) :
    (0 ≤ B.torusUpperApprox rho v ∧ B.torusUpperApprox rho v ≤ 1) ∧
      (0 ≤ B.torusLowerApprox rho v ∧ B.torusLowerApprox rho v ≤ 1) :=
  ⟨torusChordCutoff_range _ _ _, torusChordCutoff_range _ _ _⟩

theorem torus_approximations_lipschitz (B : Set N) (hB : 0 < B.radius)
    (rho : ℝ≥0) (hrho : 0 < rho) :
    LipschitzWith (((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant)
      (B.torusUpperApprox rho) ∧
    LipschitzWith (((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant)
      (B.torusLowerApprox rho) := by
  constructor <;> simpa only [rank, Fintype.card_coe, torusUpperApprox, torusLowerApprox] using
    torusChordCutoff_lipschitz (ι := B.frequencies) _ _ (B.approximationWidth_pos hB rho hrho)

theorem exists_torus_approximation_orbit (B : Set N) (rho : ℝ≥0) :
    ∃ theta : B.frequencies → ℝ, ∀ x z : ZMod N,
      B.torusUpperApprox rho
          (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) =
        B.upperApprox rho (x - z) ∧
      B.torusLowerApprox rho
          (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) =
        B.lowerApprox rho (x - z) := by
  obtain ⟨theta, htheta⟩ := exists_real_frequency_phases B
  refine ⟨theta, ?_⟩
  intro x z
  have hcoords :
      (fun r : B.frequencies => CircleFourier.character
        ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) =
      (fun r : B.frequencies => character r (x - z)) := funext (htheta x z)
  constructor <;> simp only [torusUpperApprox, torusLowerApprox, torusChordCutoff,
    upperApprox, lowerApprox, hcoords]

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalTorus

open Module

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct NNReal

end Erdos3.RationalTorus

end

section

namespace Erdos3.CircleFourier

end Erdos3.CircleFourier

namespace Erdos3.RationalTorus

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable (d : ℕ)
  [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]

end Erdos3.RationalTorus

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}

variable (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)

variable (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

end Erdos3

end

section

namespace Erdos3.RationalTorus

open scoped BigOperators TensorProduct NNReal

variable {σ : Type*} [Fintype σ] (d : ℕ)

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b : Fin d → ℝ) (a : σ → Fin d → ℝ)
  (Ψ : (Fin d → CircleFourier.Circle) → ℂ) (M K : ℝ≥0)
  (hΨ : ∀ v, ‖Ψ v‖ ≤ M) (hLip : LipschitzWith K Ψ)

end Erdos3.RationalTorus

end

section

namespace Erdos3

open RationalFilteredNilmanifold CircleFourier
open scoped TensorProduct NNReal

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct NNReal

namespace RationalTorus

variable {ι : Type*} [Fintype ι] {d : ℕ} (e : ι ≃ Fin d)
  (Ψ : (ι → CircleFourier.Circle) → ℝ)

variable [TopologicalSpace (ℝ ⊗[ℚ] Algebra d)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra d)] [T2Space (ℝ ⊗[ℚ] Algebra d)]
  (b a : ι → ℝ) (K : ℝ≥0)
  (hΨ : ∀ v, 0 ≤ Ψ v ∧ Ψ v ≤ 1) (hLip : LipschitzWith K Ψ)

end RationalTorus
end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem approximationComplexity_nonneg (B : Set N) (rho : ℝ≥0) :
    0 ≤ B.approximationComplexity rho :=
  (Nat.cast_nonneg B.rank).trans (le_max_left _ _)

theorem exists_upperApprox_niltest (B : Set N) (hB : 0 < B.radius)
    (rho : ℝ≥0) (hrho : 0 < rho) (z : ZMod N) :
    ∃ T : (RationalTorus.nilmanifold B.rank).Niltest (fun _ : Unit => 1),
      T.UnitIntervalValued ∧ T.ComplexityLE (B.approximationComplexity rho) ∧
      ∀ x : ZMod N, T.evalCyclic N (fun _ => x) = (B.upperApprox rho (x - z) : ℂ) := by
  obtain ⟨theta, htheta⟩ := B.exists_torus_approximation_orbit rho
  have hΨ : ∀ v, 0 ≤ B.torusUpperApprox rho v ∧ B.torusUpperApprox rho v ≤ 1 :=
    fun v => (B.torus_approximation_ranges rho v).1
  have hLip : LipschitzWith (B.approximationLipBound rho) (B.torusUpperApprox rho) :=
    (B.torus_approximations_lipschitz hB rho hrho).1
  let e : B.frequencies ≃ Fin B.rank := B.frequencies.equivFin
  let b : B.frequencies → ℝ := fun r => -(z.val : ℝ) * theta r
  let T := RationalTorus.realAffineNiltest e (B.torusUpperApprox rho) b theta
    (B.approximationLipBound rho) hΨ hLip
  refine ⟨T, ?_, ?_, ?_⟩
  · exact RationalTorus.realAffineNiltest_unitInterval e (B.torusUpperApprox rho) b theta
      (B.approximationLipBound rho) hΨ hLip
  · exact RationalTorus.realAffineNiltest_complexity e (B.torusUpperApprox rho) b theta
      (B.approximationLipBound rho) hΨ hLip (B.approximationComplexity_nonneg rho)
      (le_max_left _ _) (le_max_right _ _)
  · intro x
    dsimp only [T]
    rw [RationalTorus.realAffineNiltest_evalCyclic]
    have hphase : (fun r => ((b r + (x.val : ℝ) * theta r : ℝ) : CircleFourier.Circle)) =
        (fun r => ((((x.val : ℝ) - (z.val : ℝ)) * theta r : ℝ) : CircleFourier.Circle)) := by
      funext r
      congr 1
      dsimp [b]
      ring
    rw [hphase, (htheta x z).1]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem upperApprox_comparison_of_niltests
    (B : Set N) (hB : 0 < B.radius) (rho : ℝ≥0) (hrho : 0 < rho)
    (f g : ZMod N → ℝ) {P epsilon : ℝ}
    (hbudget : B.approximationComplexity rho ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P epsilon f g) (z : ZMod N) :
    (𝔼 x, B.upperApprox rho (x - z) * (f x - g x)) ≤ epsilon := by
  obtain ⟨T, hunit, hT, hEval⟩ := B.exists_upperApprox_niltest hB rho hrho z
  have h := hcompare (RationalTorus.nilmanifold B.rank) le_rfl T hunit (hT.mono hbudget)
  simpa only [hEval, Complex.ofReal_re, mul_comm] using h

theorem small_sum_average_of_niltest_comparison
    (B : Set N) (hBpos : 0 < B.radius) (hB : B.IsRankRegular)
    (f g : ZMod N → ℝ) {W eta P epsilon : ℝ} (hW : 0 ≤ W) (heta : 0 < eta)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hepsilon : epsilon ≤ (eta / 2) * ((B.carrier.card : ℝ) / N))
    (hbudget : B.approximationComplexity (localizedAverageScale B.rank W (eta / 2)) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P epsilon f g) (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ eta := by
  apply B.small_sum_average_of_upperApprox hBpos hB f g hW heta hf hg hepsilon
  intro y
  exact B.upperApprox_comparison_of_niltests hBpos _
    (localizedAverageScale_spec B.rank hW (by positivity)).1 f g hbudget hcompare y

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem coe_approximationLipBound (B : Set N) (rho : ℝ≥0) :
    (B.approximationLipBound rho : ℝ) =
      (B.rank : ℝ) / ((rho : ℝ) * B.radius) * (2 * Real.pi) := by
  have hwidth : (B.approximationWidth rho : ℝ) = (rho : ℝ) * B.radius := rfl
  unfold approximationLipBound
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv,
    hwidth, CircleFourier.coe_characterLipConstant, div_eq_mul_inv]

theorem approximationComplexity_exp_le (B : Set N) (rho : ℝ≥0) {Q R : ℝ}
    (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hrho : Real.exp (-Q) ≤ (rho : ℝ)) (hwidth : Real.exp (-R) ≤ B.radius) :
    B.approximationComplexity rho ≤ (B.rank : ℝ) + Q + R + 12 := by
  have hrhopos : 0 < (rho : ℝ) := (Real.exp_pos _).trans_le hrho
  have hwpos : 0 < B.radius := (Real.exp_pos _).trans_le hwidth
  have hprod : Real.exp (-(Q + R)) ≤ (rho : ℝ) * B.radius := by
    calc
      _ = Real.exp (-Q) * Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hrho hwidth (Real.exp_nonneg _) hrhopos.le
  have hinv : ((rho : ℝ) * B.radius)⁻¹ ≤ Real.exp (Q + R) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos _) hprod
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have hrank : (B.rank : ℝ) ≤ Real.exp (B.rank : ℝ) := by
    linarith [Real.add_one_le_exp (B.rank : ℝ)]
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by linarith [Real.pi_lt_four]
  have hK : (B.approximationLipBound rho : ℝ) ≤
      8 * Real.exp ((B.rank : ℝ) + Q + R) := by
    rw [coe_approximationLipBound, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (B.rank : ℝ) * Real.exp (Q + R) * 8 := by gcongr
      _ = _ := by rw [← Real.exp_add, ← add_assoc, mul_comm]
  have hone : 1 ≤ Real.exp ((B.rank : ℝ) + Q + R) :=
    Real.one_le_exp (by positivity)
  change max (B.rank : ℝ) (Real.log (3 + (B.approximationLipBound rho : ℝ))) ≤ _
  apply max_le
  · linarith
  · apply (Real.log_le_iff_le_exp (by positivity)).mpr
    calc
      _ ≤ 11 * Real.exp ((B.rank : ℝ) + Q + R) := by linarith
      _ ≤ Real.exp 12 * Real.exp ((B.rank : ℝ) + Q + R) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 12]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem card_ratio_ge_exp_width (B : Set N) (hB1 : B.radius ≤ 1) {R : ℝ}
    (hwidth : Real.exp (-R) ≤ B.radius) :
    Real.exp (-((B.rank : ℝ) * (R + 10))) ≤ (B.carrier.card : ℝ) / N := by
  have hB : 0 < B.radius := (Real.exp_pos _).trans_le hwidth
  have hbase : Real.exp (-(R + 10)) ≤ B.radius / 10 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).mpr
    calc
      _ ≤ Real.exp (-(R + 10)) * Real.exp 10 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 10]
      _ = Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hwidth
  have hpower : Real.exp (-((B.rank : ℝ) * (R + 10))) ≤ (B.radius / 10) ^ B.rank := by
    calc
      _ = Real.exp (-(R + 10)) ^ B.rank := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hbase _
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  apply (le_div_iff₀ hN).mpr
  exact (mul_le_mul_of_nonneg_right hpower hN.le).trans (card_lower_bound B hB hB1)

theorem small_sum_average_of_exponential_niltest_comparison
    (B : Set N) (hB : B.IsRankRegular) (hB1 : B.radius ≤ 1)
    (f g : ZMod N → ℝ) {W A E R P : ℝ}
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hWcap : W ≤ Real.exp A) (hwidth : Real.exp (-R) ≤ B.radius)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ W)
    (hcomplexity : 2 * (B.rank : ℝ) + A + E + R + 1612 ≤ P)
    (hprecision : E + 2 + (B.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) f g) (z : ZMod N) :
    (𝔼 s ∈ B.carrier, 𝔼 t ∈ B.carrier, (f (z + s + t) - g (z + s + t))) ≤ Real.exp (-E) := by
  have hBpos : 0 < B.radius := (Real.exp_pos _).trans_le hwidth
  have hbudget : B.approximationComplexity
      (localizedAverageScale B.rank W (Real.exp (-E) / 2)) ≤ P := by
    have h := B.approximationComplexity_exp_le _
      (show 0 ≤ (B.rank : ℝ) + A + E + 1600 by positivity) hR
      (localizedAverageScale_exp_lower B.rank hW hWcap hA hE) hwidth
    exact h.trans (by linarith)
  have hhalf : Real.exp (-(E + 2)) ≤ Real.exp (-E) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-(E + 2)) * Real.exp 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp 2]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have herror : Real.exp (-P) ≤ (Real.exp (-E) / 2) * ((B.carrier.card : ℝ) / N) := by
    calc
      _ ≤ Real.exp (-(E + 2 + (B.rank : ℝ) * (R + 10))) :=
        Real.exp_le_exp.mpr (neg_le_neg hprecision)
      _ = Real.exp (-(E + 2)) * Real.exp (-((B.rank : ℝ) * (R + 10))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul hhalf (B.card_ratio_ge_exp_width hB1 hwidth)
        (Real.exp_nonneg _) (by positivity)
  exact B.small_sum_average_of_niltest_comparison hBpos hB f g hW (Real.exp_pos _)
    hf hg herror hbudget hcompare z

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.MatchedFlatNiltest
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {N : ℕ} [NeZero N]

theorem matched_flat_integral_of_niltest_comparison
    (L : Finset (ZMod N)) (S : CyclicBohr.Set N)
    (hS : S.IsRankRegular) (hS1 : S.radius ≤ 1)
    (A B f g : ZMod N → ℝ) (z : ZMod N)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    {epsilon p C D R P M : ℝ} (hepsilon : 0 < epsilon) (hp : 1 ≤ p)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hMcap : M ≤ Real.exp (C * p)) (hwidth : Real.exp (-R) ≤ S.radius)
    {q : ℕ} (hq : 0 < q)
    (horder : (1 + C + (D + 1) + Real.log 3) * p ≤ (q : ℝ) * Real.log 2)
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ Real.exp p)
    (hB : ∀ x, 0 ≤ B x ∧ B x ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S.carrier
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤
        flatComparisonDelta epsilon)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B) :
    matchedIntegral L S.carrier (fun x => A (z + x) - (1 + epsilon) * B (z + x)) f g ≤
      Real.exp (-(D * p)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hp0 : 0 ≤ p := by linarith
  have hE : 0 ≤ (D + 2) * p := by positivity
  have hmean := S.small_sum_average_of_exponential_niltest_comparison hS hS1 A B
    (Real.exp_nonneg p) hp0 hE hR le_rfl hwidth
    (fun x => (hA x).1) (fun x => (hB x).2) hcomplexity hprecision hcompare z
  obtain ⟨hdelta, hdelta4, hcoeff⟩ := flatComparisonDelta_spec hepsilon
  have heta : Real.exp (-((D + 2) * p)) ≤ Real.exp (-(D * p)) / 4 := by
    have hfirst := exp_extra_decay_le_half (D := D + 1) hp
    have hsecond := exp_extra_decay_le_half (D := D) hp
    have heq : D + 1 + 1 = D + 2 := by ring
    rw [heq] at hfirst
    linarith
  apply matched_flat_integral_decay L S.carrier
    (fun x => A (z + x)) (fun x => B (z + x)) f g hu hv hu1 hv1 hq
    (Real.exp_nonneg p) hM hepsilon.le hdelta (hdelta4.trans (by norm_num)) hcoeff
    hp hC (by simp only [one_mul, le_refl]) hMcap heta horder
    (fun x => hA (z + x)) (fun x => hB (z + x)) hf hg hgcap hfsupport hfmean hflat
  simpa only [add_assoc] using hmean

end Erdos3.CellRefinement

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.CellRefinement.matched_flat_integral_of_niltest_comparison := @OAI.Erdos3.CellRefinement.matched_flat_integral_of_niltest_comparison
