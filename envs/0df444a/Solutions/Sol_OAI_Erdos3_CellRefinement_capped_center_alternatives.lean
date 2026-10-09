-- Prove2me | solution 1 for OAI.Erdos3.CellRefinement.capped_center_alternatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:09:14.181982+00:00
-- url     : https://prove2.me/submissions/72507778-fb89-4cc4-a932-7bd292c95989

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034
import Theorems.Thm_OAI_Erdos3_CellRefinement_matched_flat_integral_of_niltest_comparison
import Theorems.Thm_OAI_Erdos3_LocalConvolution_exists_parent_unbalanced_independent_refinement

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

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

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

theorem cellAverage_le [Add G] {C : Finset G} (hC : C.Nonempty) (f : G → ℝ)
    {M : ℝ} (hf : ∀ x, f x ≤ M) (x : G) : cellAverage C f x ≤ M :=
  (Finset.expect_le_expect (fun c (_ : c ∈ C) => hf (x + c))).trans_eq (Finset.expect_const hC M)

variable [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BinomialMomentAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pow_le_choose_block (R n : ℕ) :
    (R : ℝ) ^ n ≤ (((R + 1) * n).choose n : ℝ) := by
  have hchoose := Nat.pow_le_choose (α := ℝ) n ((R + 1) * n)
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hbase : R * n ≤ (R + 1) * n + 1 - n := by
    rw [Nat.add_mul, one_mul]
    omega
  have hbaseR : (R : ℝ) * n ≤ (((R + 1) * n + 1 - n : ℕ) : ℝ) := by exact_mod_cast hbase
  have hfirst : (R : ℝ) ^ n ≤
      ((((R + 1) * n + 1 - n : ℕ) : ℝ) ^ n) / (n.factorial : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast Nat.factorial_pos n : (0 : ℝ) < n.factorial)).mpr
    calc
      (R : ℝ) ^ n * (n.factorial : ℝ) ≤ (R : ℝ) ^ n * (n : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = ((R : ℝ) * n) ^ n := (mul_pow _ _ _).symm
      _ ≤ (((R + 1) * n + 1 - n : ℕ) : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hbaseR n
  exact hfirst.trans hchoose

theorem expect_one_add_pow_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) (N : ℕ) :
    (𝔼 x ∈ s, (1 + f x) ^ N) =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (𝔼 x ∈ s, f x ^ k) := by
  have hpow (x : ι) : (1 + f x) ^ N =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * f x ^ k := by
    rw [add_comm, add_pow]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hpow]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_expect]

theorem expect_one_add_pow_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ s, f x ^ k) {n N : ℕ} (hn : n ≤ N) :
    (N.choose n : ℝ) * (𝔼 x ∈ s, f x ^ n) ≤ 𝔼 x ∈ s, (1 + f x) ^ N := by
  rw [expect_one_add_pow_eq]
  exact Finset.single_le_sum
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hmom k)) (Finset.mem_range.mpr (by omega))

theorem expect_one_add_pow_block_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ s, f x ^ k) (R n : ℕ) :
    (R : ℝ) ^ n * (𝔼 x ∈ s, f x ^ n) ≤ 𝔼 x ∈ s, (1 + f x) ^ ((R + 1) * n) := by
  apply (mul_le_mul_of_nonneg_right (pow_le_choose_block R n) (hmom n)).trans
  apply expect_one_add_pow_lower s f hmom
  nlinarith

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

theorem finiteSetLp_eq_sum (s : Finset ι) (f : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s f p =
      (∑ i ∈ s, |f i| ^ p) ^ (1 / (p : ℝ)) / (s.card : ℝ) ^ (1 / (p : ℝ)) := by
  rw [finiteSetLp_of_pos s f hp, Finset.expect_eq_sum_div_card,
    Real.div_rpow (Finset.sum_nonneg (fun _ _ => by positivity)) (Nat.cast_nonneg _)]

theorem finiteSetLp_const {s : Finset ι} (hs : s.Nonempty) (c : ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s (fun _ => c) p = |c| := by
  rw [finiteSetLp_of_pos s (fun _ => c) hp, Finset.expect_const hs]
  simpa only [one_div] using Real.pow_rpow_inv_natCast (abs_nonneg c) hp.ne'

theorem finiteSetLp_mono_abs (s : Finset ι) (f g : ι → ℝ) {p : ℕ} (hp : 0 < p)
    (hfg : ∀ i ∈ s, |f i| ≤ |g i|) :
    finiteSetLp s f p ≤ finiteSetLp s g p := by
  rw [finiteSetLp_of_pos s f hp, finiteSetLp_of_pos s g hp]
  apply Real.rpow_le_rpow (Finset.expect_nonneg (fun _ _ => by positivity))
  · exact Finset.expect_le_expect (fun i hi => pow_le_pow_left₀ (abs_nonneg _) (hfg i hi) p)
  · positivity

theorem finiteSetLp_le_of_bound {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) {p : ℕ} (hp : 0 < p) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ i ∈ s, |f i| ≤ M) : finiteSetLp s f p ≤ M := by
  have h := finiteSetLp_mono_abs s f (fun _ => M) hp
    (fun i hi => by simpa only [abs_of_nonneg hM] using hf i hi)
  simpa only [finiteSetLp_const hs M hp, abs_of_nonneg hM] using h

theorem finiteSetLp_add_le (s : Finset ι) (f g : ι → ℝ) {p : ℕ} (hp : 0 < p) :
    finiteSetLp s (fun i => f i + g i) p ≤ finiteSetLp s f p + finiteSetLp s g p := by
  simp only [finiteSetLp_eq_sum s _ hp]
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h := Real.Lp_add_le s f g hpR
  simp only [Real.rpow_natCast] at h
  have hd : 0 ≤ (s.card : ℝ) ^ (1 / (p : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  simpa only [add_div] using div_le_div_of_nonneg_right h hd

theorem finiteSetLp_le_of_uniform_error {s : Finset ι} (hs : s.Nonempty)
    (f g : ι → ℝ) {p : ℕ} (hp : 0 < p) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ i ∈ s, |f i - g i| ≤ epsilon) :
    finiteSetLp s f p ≤ finiteSetLp s g p + epsilon := by
  have h := finiteSetLp_add_le s g (fun i => f i - g i) hp
  have heq : (fun i => g i + (f i - g i)) = f := by funext i; ring
  rw [heq] at h
  exact h.trans (add_le_add le_rfl (finiteSetLp_le_of_bound hs _ hp hepsilon herror))

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem convolution_add (L : Finset G) (f g : G → ℝ) (s t : G) :
    convolution L f g (s + t) = (∑ x, f (s - x) * g (t + x)) / L.card := by
  unfold convolution
  congr 1
  apply Fintype.sum_equiv (Equiv.subLeft s)
  intro x
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  congr 1
  congr 1
  abel

theorem correlation_sub (L : Finset G) (f g : G → ℝ) (s t : G) :
    correlation L f g (s - t) = (∑ x, f (s - x) * g (t - x)) / L.card := by
  unfold correlation
  congr 1
  apply Fintype.sum_equiv (Equiv.subLeft t)
  intro x
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  congr 1
  congr 1
  abel

omit [Fintype G] in
theorem plusMomentVector_eq_neg (S : Finset G) (f : G → ℝ) (j : ℕ) (v : Fin j → G) :
    plusMomentVector S f j v = momentVector S f j (-v) := by
  simp only [plusMomentVector, momentVector, Pi.neg_apply, sub_neg_eq_add]

theorem sum_momentVector_mul (S : Finset G) (f g : G → ℝ) (j : ℕ) :
    (∑ v : Fin j → G, momentVector S f j v * momentVector S g j v) =
      𝔼 s ∈ S, 𝔼 t ∈ S, (∑ x : G, f (s - x) * g (t - x)) ^ j := by
  unfold momentVector
  simp_rw [Finset.expect_mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro s _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro t _
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

theorem sum_momentVector_mul_plus (S : Finset G) (f g : G → ℝ) (j : ℕ) :
    (∑ v : Fin j → G, momentVector S f j v * plusMomentVector S g j v) =
      𝔼 s ∈ S, 𝔼 t ∈ S, (∑ x : G, f (s - x) * g (t + x)) ^ j := by
  unfold momentVector plusMomentVector
  simp_rw [Finset.expect_mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro s _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro t _
  rw [Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]

theorem sum_sq_plusMomentVector (S : Finset G) (f : G → ℝ) (j : ℕ) :
    (∑ v : Fin j → G, plusMomentVector S f j v ^ 2) =
      ∑ v : Fin j → G, momentVector S f j v ^ 2 := by
  simp_rw [plusMomentVector_eq_neg]
  exact Fintype.sum_equiv (Equiv.neg (Fin j → G)) _ _ (fun _ => rfl)

theorem differenceMoment_correlation_eq (L S : Finset G) (f g : G → ℝ) (j : ℕ) :
    differenceMoment S (correlation L f g) j =
      (∑ v : Fin j → G, momentVector S f j v * momentVector S g j v) / (L.card : ℝ) ^ j := by
  unfold differenceMoment
  simp_rw [correlation_sub, div_pow, ← Finset.expect_div]
  rw [sum_momentVector_mul]

theorem sumMoment_convolution_eq (L S : Finset G) (f g : G → ℝ) (j : ℕ) :
    sumMoment S (convolution L f g) j =
      (∑ v : Fin j → G, momentVector S f j v * plusMomentVector S g j v) / (L.card : ℝ) ^ j := by
  unfold sumMoment
  simp_rw [convolution_add, div_pow, ← Finset.expect_div]
  rw [sum_momentVector_mul_plus]

theorem differenceMoment_self_nonneg (L S : Finset G) (f : G → ℝ) (j : ℕ) :
    0 ≤ differenceMoment S (correlation L f f) j := by
  rw [differenceMoment_correlation_eq]
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) (by positivity)

theorem sumMoment_convolution_sq_le (L S : Finset G) (f g : G → ℝ) (j : ℕ) :
    sumMoment S (convolution L f g) j ^ 2 ≤
      differenceMoment S (correlation L f f) j * differenceMoment S (correlation L g g) j := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (momentVector S f j) (plusMomentVector S g j)
  rw [sum_sq_plusMomentVector] at hCS
  have h := div_le_div_of_nonneg_right hCS (sq_nonneg ((L.card : ℝ) ^ j))
  rw [sumMoment_convolution_eq, differenceMoment_correlation_eq, differenceMoment_correlation_eq]
  simpa only [div_pow, pow_two, div_mul_div_comm] using h

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem momentAmplificationFactor_pos (delta : ℝ) : 0 < momentAmplificationFactor delta := by
  unfold momentAmplificationFactor
  omega

theorem momentAmplificationGain_pos (delta : ℝ) : 0 < momentAmplificationGain delta := by
  have hR : (0 : ℝ) < momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / (momentAmplificationFactor delta : ℝ))
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_le_one (delta : ℝ) : momentAmplificationGain delta ≤ 1 := by
  have hR : (1 : ℝ) ≤ momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have hinv : 1 / (momentAmplificationFactor delta : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hR
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hinv
  rw [Real.rpow_one] at h
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_pow (delta : ℝ) :
    (1 + momentAmplificationGain delta) ^ momentAmplificationFactor delta = 2 := by
  unfold momentAmplificationGain
  rw [← add_sub_assoc, add_sub_cancel_left, one_div]
  exact Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 2) (momentAmplificationFactor_pos delta).ne'

theorem finiteSetLp_unbalance {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {n : ℕ} (hn : 0 < n) (heven : Even n)
    (hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ s, f x ^ k)
    (hlarge : delta ≤ finiteSetLp s f n) :
    1 + momentAmplificationGain delta ≤
      finiteSetLp s (fun x => 1 + f x) (momentAmplificationFactor delta * n) := by
  let R : ℕ := ⌈2 / delta⌉₊
  have hR : 2 ≤ (R : ℝ) * delta :=
    (div_le_iff₀ hdelta).mp (Nat.le_ceil (2 / delta))
  have hmoment : delta ^ n ≤ 𝔼 x ∈ s, f x ^ n := by
    have h := pow_le_pow_left₀ hdelta.le hlarge n
    rw [finiteSetLp_pow s f hn] at h
    simpa only [heven.pow_abs] using h
  have hN : 0 < momentAmplificationFactor delta * n :=
    Nat.mul_pos (momentAmplificationFactor_pos delta) hn
  have hmomentLarge : (2 : ℝ) ^ n ≤
      𝔼 x ∈ s, (1 + f x) ^ (momentAmplificationFactor delta * n) := by
    calc
      (2 : ℝ) ^ n ≤ ((R : ℝ) * delta) ^ n := pow_le_pow_left₀ (by norm_num) hR n
      _ = (R : ℝ) ^ n * delta ^ n := mul_pow _ _ _
      _ ≤ (R : ℝ) ^ n * (𝔼 x ∈ s, f x ^ n) :=
        mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ ≤ 𝔼 x ∈ s, (1 + f x) ^ (momentAmplificationFactor delta * n) :=
        expect_one_add_pow_block_lower s f hmom R n
  apply le_of_pow_le_pow_left₀ hN.ne' (finiteSetLp_nonneg _ _ _)
  calc
    (1 + momentAmplificationGain delta) ^ (momentAmplificationFactor delta * n) = (2 : ℝ) ^ n := by
      rw [pow_mul, momentAmplificationGain_pow]
    _ ≤ 𝔼 x ∈ s, (1 + f x) ^ (momentAmplificationFactor delta * n) := hmomentLarge
    _ ≤ 𝔼 x ∈ s, |1 + f x| ^ (momentAmplificationFactor delta * n) := by
      apply Finset.expect_le_expect
      intro x _
      simpa only [abs_pow] using le_abs_self ((1 + f x) ^ (momentAmplificationFactor delta * n))
    _ = finiteSetLp s (fun x => 1 + f x) (momentAmplificationFactor delta * n) ^
        (momentAmplificationFactor delta * n) := (finiteSetLp_pow _ _ hN).symm

end Erdos3.LocalConvolution

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem differenceLp_nonneg (S : Finset G) (f : G → ℝ) (p : ℕ) : 0 ≤ differenceLp S f p :=
  finiteSetLp_nonneg _ _ _

theorem sumLp_pow (S : Finset G) (f : G → ℝ) {p : ℕ} (hp : 0 < p) (heven : Even p) :
    sumLp S f p ^ p = sumMoment S f p := by
  rw [sumLp, finiteSetLp_pow _ _ hp, Finset.expect_product]
  simp only [heven.pow_abs, sumMoment]

theorem differenceLp_pow (S : Finset G) (f : G → ℝ) {p : ℕ} (hp : 0 < p) (heven : Even p) :
    differenceLp S f p ^ p = differenceMoment S f p := by
  rw [differenceLp, finiteSetLp_pow _ _ hp, Finset.expect_product]
  simp only [heven.pow_abs, differenceMoment]

theorem sumLp_le_of_uniform_error {S : Finset G} (hS : S.Nonempty) (f g : G → ℝ)
    {p : ℕ} (hp : 0 < p) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ s ∈ S, ∀ t ∈ S, |f (s + t) - g (s + t)| ≤ epsilon) :
    sumLp S f p ≤ sumLp S g p + epsilon := by
  apply finiteSetLp_le_of_uniform_error (hS.product hS) _ _ hp hepsilon
  intro x hx
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hx
  exact herror x.1 hs x.2 ht

theorem differenceLp_le_of_uniform_error {S : Finset G} (hS : S.Nonempty) (f g : G → ℝ)
    {p : ℕ} (hp : 0 < p) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (herror : ∀ s ∈ S, ∀ t ∈ S, |f (s - t) - g (s - t)| ≤ epsilon) :
    differenceLp S f p ≤ differenceLp S g p + epsilon := by
  apply finiteSetLp_le_of_uniform_error (hS.product hS) _ _ hp hepsilon
  intro x hx
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hx
  exact herror x.1 hs x.2 ht

theorem convolution_sumLp_sq_le [Fintype G] (L S : Finset G) (f g : G → ℝ)
    {m : ℕ} (hm : 0 < m) :
    sumLp S (convolution L f g) (2 * m) ^ 2 ≤
      differenceLp S (correlation L f f) (2 * m) * differenceLp S (correlation L g g) (2 * m) := by
  have hp : 0 < 2 * m := by omega
  have heven : Even (2 * m) := ⟨m, by omega⟩
  have hCS := sumMoment_convolution_sq_le L S f g (2 * m)
  rw [← sumLp_pow S (convolution L f g) hp heven,
    ← differenceLp_pow S (correlation L f f) hp heven,
    ← differenceLp_pow S (correlation L g g) hp heven] at hCS
  apply le_of_pow_le_pow_left₀ hp.ne'
    (mul_nonneg (differenceLp_nonneg _ _ _) (differenceLp_nonneg _ _ _))
  calc
    (sumLp S (convolution L f g) (2 * m) ^ 2) ^ (2 * m) =
        (sumLp S (convolution L f g) (2 * m) ^ (2 * m)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    _ ≤ _ := hCS
    _ = _ := (mul_pow _ _ _).symm

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem abs_sum_mul_sub_le {ι : Type*} [Fintype ι] (u v f : ι → ℝ) {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) :
    |(∑ x, u x * f x) - ∑ x, v x * f x| ≤ M * ∑ x, |u x - v x| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |u x * f x - v x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |u x - v x| * |f x| := by simp only [← sub_mul, abs_mul]
    _ ≤ ∑ x, |u x - v x| * M :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _))
    _ = M * ∑ x, |u x - v x| := by rw [← Finset.sum_mul]; ring

namespace LocalConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem correlation_swap (L : Finset G) (f g : G → ℝ) (t : G) :
    correlation L f g t = correlation L g f (-t) := by
  unfold correlation
  congr 1
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro x
  simp [mul_comm]

theorem correlation_sub_self (L : Finset G) (f g : G → ℝ) (t : G) :
    correlation L (fun x => f x - g x) (fun x => f x - g x) t =
      correlation L f f t - correlation L f g t - correlation L g f t + correlation L g g t := by
  unfold correlation
  simp_rw [sub_mul, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

variable [DecidableEq G]

omit [AddCommGroup G] [Fintype G] in
theorem indicator_div_card (L : Finset G) (x : G) :
    realFinsetIndicator L x / (L.card : ℝ) = realUniformMass L x := by
  by_cases hx : x ∈ L <;> simp [realFinsetIndicator, realUniformMass, hx, one_div]

omit [AddCommGroup G] in
theorem sum_uniformMass_mul_eq_one {L : Finset G} (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card) :
    ∑ x, realUniformMass L x * f x = 1 := by
  have hcard : (L.card : ℝ) ≠ 0 := by exact_mod_cast hL.card_pos.ne'
  have hpoint (x : G) : realUniformMass L x * f x = f x / L.card := by
    by_cases hx : x ∈ L
    · simp [realUniformMass, hx, div_eq_mul_inv, mul_comm]
    · simp [realUniformMass, hx, hsupport x hx]
  simp_rw [hpoint]
  rw [← Finset.sum_div, hsum, div_self hcard]

theorem correlation_indicator_left_eq (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L (realFinsetIndicator L) f t = ∑ x, realUniformMass L (x + t) * f x := by
  rw [correlation, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [← div_mul_eq_mul_div, indicator_div_card]

theorem correlation_indicator_right_eq (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L f (realFinsetIndicator L) t = ∑ x, realUniformMass L (x - t) * f x := by
  rw [correlation_swap, correlation_indicator_left_eq]
  simp only [sub_eq_add_neg]

theorem convolution_indicator_eq (L : Finset G)
    (hsymm : ∀ x, -x ∈ L ↔ x ∈ L) (f : G → ℝ) (t : G) :
    convolution L (realFinsetIndicator L) f t = ∑ x, realUniformMass L (x - t) * f x := by
  rw [convolution, Finset.sum_div]
  apply Fintype.sum_equiv (Equiv.subLeft t)
  intro x
  have hindex : (t - x) - t = -x := by abel
  have hneg : realUniformMass L (-x) = realUniformMass L x := by
    simp [realUniformMass, hsymm x]
  simp only [Equiv.subLeft_apply, hindex, hneg]
  rw [← div_mul_eq_mul_div, indicator_div_card]

theorem correlation_indicator_right_sub_one_le {L : Finset G} (hL : L.Nonempty)
    (f : G → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) (t : G) :
    |correlation L f (realFinsetIndicator L) t - 1| ≤
      M * ∑ x, |realUniformMass L (x - t) - realUniformMass L x| := by
  rw [correlation_indicator_right_eq, ← sum_uniformMass_mul_eq_one hL f hsupport hsum]
  exact abs_sum_mul_sub_le _ _ _ hf

theorem convolution_indicator_sub_one_le {L : Finset G} (hL : L.Nonempty)
    (hsymm : ∀ x, -x ∈ L ↔ x ∈ L) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) (t : G) :
    |convolution L (realFinsetIndicator L) f t - 1| ≤
      M * ∑ x, |realUniformMass L (x - t) - realUniformMass L x| := by
  rw [convolution_indicator_eq L hsymm, ← sum_uniformMass_mul_eq_one hL f hsupport hsum]
  exact abs_sum_mul_sub_le _ _ _ hf

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem convolution_sub_left (L : Finset G) (f h g : G → ℝ) (t : G) :
    convolution L (fun x => f x - h x) g t = convolution L f g t - convolution L h g t := by
  unfold convolution
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, sub_div]

variable [DecidableEq G]

omit [AddCommGroup G] in
theorem normalized_cap_ge_one {L : Finset G} (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) : 1 ≤ M := by
  calc
    1 = ∑ x, realUniformMass L x * f x := (sum_uniformMass_mul_eq_one hL f hsupport hsum).symm
    _ ≤ ∑ x, realUniformMass L x * M := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hf x)) (realUniformMass_nonneg L x)
    _ = M := by rw [← Finset.sum_mul, sum_realUniformMass hL, one_mul]

omit [DecidableEq G] in
theorem centered_convolution_error (L : Finset G) (f g : G → ℝ) (t : G) :
    (convolution L f g t - 1) - convolution L (balancedFunction L f) g t =
      convolution L (realFinsetIndicator L) g t - 1 := by
  unfold balancedFunction
  rw [convolution_sub_left]
  ring

omit [DecidableEq G] in
theorem centered_correlation_error_identity (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L f f t - (1 + correlation L (balancedFunction L f) (balancedFunction L f) t) =
      (correlation L f (realFinsetIndicator L) t - 1) +
      (correlation L (realFinsetIndicator L) f t - 1) -
      (correlation L (realFinsetIndicator L) (realFinsetIndicator L) t - 1) := by
  unfold balancedFunction
  rw [correlation_sub_self]
  ring

theorem centered_correlation_error_le {L : Finset G} (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) (hsum : ∑ x, f x = L.card)
    {M eta : ℝ} (hf : ∀ x, |f x| ≤ M) (heta : 0 ≤ eta) (t : G)
    (hTV : (∑ x, |realUniformMass L (x - t) - realUniformMass L x|) ≤ eta)
    (hTVneg : (∑ x, |realUniformMass L (x - (-t)) - realUniformMass L x|) ≤ eta) :
    |correlation L f f t - (1 + correlation L (balancedFunction L f) (balancedFunction L f) t)| ≤
      3 * M * eta := by
  have hM1 := normalized_cap_ge_one hL f hsupport hsum hf
  have hM : 0 ≤ M := by linarith
  have hright : |correlation L f (realFinsetIndicator L) t - 1| ≤ M * eta :=
    (correlation_indicator_right_sub_one_le hL f hsupport hsum hf t).trans
      (mul_le_mul_of_nonneg_left hTV hM)
  have hleft : |correlation L (realFinsetIndicator L) f t - 1| ≤ M * eta := by
    rw [correlation_swap]
    exact (correlation_indicator_right_sub_one_le hL f hsupport hsum hf (-t)).trans
      (mul_le_mul_of_nonneg_left hTVneg hM)
  have hIsupport : ∀ x, x ∉ L → realFinsetIndicator L x = 0 := by
    intro x hx
    simp [realFinsetIndicator, hx]
  have hIsum : ∑ x, realFinsetIndicator L x = L.card := by simp [realFinsetIndicator]
  have hIbound : ∀ x, |realFinsetIndicator L x| ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ L <;> simp [realFinsetIndicator, hx]
  have hind : |correlation L (realFinsetIndicator L) (realFinsetIndicator L) t - 1| ≤ eta := by
    have h := correlation_indicator_right_sub_one_le hL (realFinsetIndicator L) hIsupport hIsum hIbound t
    exact (h.trans (mul_le_mul_of_nonneg_left hTV (by norm_num))).trans_eq (one_mul eta)
  rw [centered_correlation_error_identity]
  calc
    _ ≤ |correlation L f (realFinsetIndicator L) t - 1| +
        |correlation L (realFinsetIndicator L) f t - 1| +
        |correlation L (realFinsetIndicator L) (realFinsetIndicator L) t - 1| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * eta + M * eta + eta := add_le_add (add_le_add hright hleft) hind
    _ ≤ 3 * M * eta := by nlinarith [mul_le_mul_of_nonneg_right hM1 heta]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

variable [AddCommGroup G]

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem localMomentExponentFactor_pos (delta : ℝ) : 0 < localMomentExponentFactor delta :=
  momentAmplificationFactor_pos _

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem local_alternatives_of_boundary
    (L S : Finset G) (hS : S.Nonempty) (f g : G → ℝ)
    {delta : ℝ} (hdelta : 0 < delta) {m : ℕ} (hm : 0 < m)
    (hconverror : ∀ s ∈ S, ∀ t ∈ S,
      |convolution L (realFinsetIndicator L) g (s + t) - 1| ≤ delta / 2)
    (hcorrerror : ∀ s ∈ S, ∀ t ∈ S,
      |correlation L f f (s - t) -
        (1 + correlation L (balancedFunction L f) (balancedFunction L f) (s - t))| ≤
          localMomentGain delta) :
    sumLp S (fun x => convolution L f g x - 1) (2 * m) ≤ delta ∨
      ∃ h : G → ℝ, (h = f ∨ h = g) ∧ ∃ m' : ℕ,
        0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
        1 + localMomentGain delta ≤ differenceLp S (correlation L h h) (2 * m') := by
  classical
  by_cases hflat : sumLp S (fun x => convolution L f g x - 1) (2 * m) ≤ delta
  · exact Or.inl hflat
  right
  have hflatgt := lt_of_not_ge hflat
  have hp : 0 < 2 * m := by omega
  have heven : Even (2 * m) := ⟨m, by omega⟩
  have hfactor := localMomentExponentFactor_pos delta
  have hgain := localMomentGain_pos delta
  have hgainhalf := localMomentGain_le_half delta
  let f₁ := balancedFunction L f
  have hcompare : sumLp S (fun x => convolution L f g x - 1) (2 * m) ≤
      sumLp S (convolution L f₁ g) (2 * m) + delta / 2 := by
    apply sumLp_le_of_uniform_error hS _ _ hp (by positivity)
    intro s hs t ht
    rw [centered_convolution_error]
    exact hconverror s hs t ht
  have hlargeConv : delta / 2 ≤ sumLp S (convolution L f₁ g) (2 * m) := by linarith
  by_cases hg : 2 ≤ differenceLp S (correlation L g g) (2 * m)
  · refine ⟨g, Or.inr rfl, m, hm, le_rfl, ?_, ?_⟩
    · nlinarith
    · exact (show 1 + localMomentGain delta ≤ 2 by linarith).trans hg
  have hCS := convolution_sumLp_sq_le L S f₁ g hm
  have hconvSq := pow_le_pow_left₀ (show 0 ≤ delta / 2 by positivity) hlargeConv 2
  have hprod := mul_le_mul_of_nonneg_left (le_of_not_ge hg)
    (differenceLp_nonneg S (correlation L f₁ f₁) (2 * m))
  have hlarge : delta ^ 2 / 8 ≤ differenceLp S (correlation L f₁ f₁) (2 * m) := by nlinarith
  have hbeta : 0 < delta ^ 2 / 8 := by positivity
  have hmom : ∀ k : ℕ, 0 ≤ 𝔼 x ∈ S ×ˢ S, correlation L f₁ f₁ (x.1 - x.2) ^ k := by
    intro k
    simpa only [Finset.expect_product, differenceMoment] using differenceMoment_self_nonneg L S f₁ k
  have hunbalance := finiteSetLp_unbalance (S ×ˢ S)
    (fun x => correlation L f₁ f₁ (x.1 - x.2)) hbeta hp heven hmom hlarge
  have hindex : momentAmplificationFactor (delta ^ 2 / 8) * (2 * m) =
      2 * (localMomentExponentFactor delta * m) := by
    unfold localMomentExponentFactor
    ring
  rw [hindex] at hunbalance
  change 1 + momentAmplificationGain (delta ^ 2 / 8) ≤
    differenceLp S (fun x => 1 + correlation L f₁ f₁ x) (2 * (localMomentExponentFactor delta * m)) at hunbalance
  have hm' : 0 < localMomentExponentFactor delta * m := Nat.mul_pos hfactor hm
  have htransfer := differenceLp_le_of_uniform_error hS
    (fun x => 1 + correlation L f₁ f₁ x) (correlation L f f)
    (show 0 < 2 * (localMomentExponentFactor delta * m) by omega) hgain.le
    (fun s hs t ht => by simpa only [f₁, abs_sub_comm] using hcorrerror s hs t ht)
  refine ⟨f, Or.inl rfl, localMomentExponentFactor delta * m, hm', ?_, le_rfl, ?_⟩
  · nlinarith
  unfold localMomentGain
  unfold localMomentGain at htransfer
  linarith

end Erdos3.LocalConvolution

end

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

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalWeightCaps
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem translated_slice_le (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : Peeling.slice L (fun t => f (x + t)) r ≤ f (x + r) := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem translated_slice_nonneg (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : 0 ≤ Peeling.slice L (fun t => f (x + t)) r := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem expect_translated_slice (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, Peeling.slice L (fun t => f (x + t)) r) = cellAverage L f x := by
  apply Finset.expect_congr rfl
  intro r hr
  simp only [Peeling.slice, hr, ite_true]

end Erdos3

end

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

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

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

theorem centerSlice_bounds (L : Finset G) (f : G → ℝ)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (x r : G) :
    0 ≤ centerSlice L f x r ∧ centerSlice L f x r ≤ 1 := by
  exact ⟨translated_slice_nonneg L f (fun t => (hf t).1) x r,
    (translated_slice_le L f (fun t => (hf t).1) x r).trans (hf (x + r)).2⟩

theorem centerSlice_supported (L : Finset G) (f : G → ℝ) (x : G) :
    ∀ r, r ∉ L → centerSlice L f x r = 0 := by
  intro r hr
  simp only [centerSlice, Peeling.slice, hr, ite_false]

theorem centerSlice_mean (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, centerSlice L f x r) = cellAverage L f x :=
  expect_translated_slice L f x

theorem centerSlice_normalized_cap (L : Finset G) (f : G → ℝ)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (x : G) {U c₀ M : ℝ}
    (hU : 0 < U) (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hcap : 1 ≤ M * (c₀ * U)) (hlower : c₀ * U ≤ cellAverage L f x) (r : G) :
    centerSlice L f x r / cellAverage L f x ≤ M := by
  have hmean : 0 < cellAverage L f x := (mul_pos hc₀ hU).trans_le hlower
  apply (div_le_iff₀ hmean).mpr
  exact (centerSlice_bounds L f hf x r).2.trans
    (hcap.trans (mul_le_mul_of_nonneg_left hlower hM))

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrLocalMomentAlternatives
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem local_alternatives_of_regular_bohr
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (S : Finset (ZMod N)) (hS : S.Nonempty) {kappa : ℝ≥0}
    (hSL : S ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f g : ZMod N → ℝ)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    (hfsum : ∑ x, f x = L.carrier.card) (hgsum : ∑ x, g x = L.carrier.card)
    {M delta : ℝ} (hf : ∀ x, |f x| ≤ M) (hg : ∀ x, |g x| ≤ M)
    (hdelta : 0 < delta)
    (hsmall : 1200 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ) * M ≤
      min (delta / 2) (localMomentGain delta))
    {m : ℕ} (hm : 0 < m) :
    sumLp S (fun x => convolution L.carrier f g x - 1) (2 * m) ≤ delta ∨
      ∃ h : ZMod N → ℝ, (h = f ∨ h = g) ∧ ∃ m' : ℕ,
        0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
        1 + localMomentGain delta ≤ differenceLp S (correlation L.carrier h h) (2 * m') := by
  have hM1 := normalized_cap_ge_one L.carrier_nonempty f hfsupport hfsum hf
  have hM : 0 ≤ M := by linarith
  let eta : ℝ := 400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hbudget : 3 * M * eta ≤ min (delta / 2) (localMomentGain delta) := by
    calc
      _ = 1200 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ) * M := by
        dsimp [eta]
        ring
      _ ≤ _ := hsmall
  have hTV (t : ZMod N) (ht : t ∈ L.ndilate (kappa + kappa)) :
      (∑ x, |realUniformMass L.carrier (x - t) - realUniformMass L.carrier x|) ≤ eta :=
    CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hL hkappa ht
  apply local_alternatives_of_boundary L.carrier S hS f g hdelta hm
  · intro s hs t ht
    have hsum : s + t ∈ L.ndilate (kappa + kappa) :=
      CyclicBohr.Set.add_mem_ndilate (hSL hs) (hSL ht)
    have hsymm : ∀ x, -x ∈ L.carrier ↔ x ∈ L.carrier := fun x => L.neg_mem_iff x
    calc
      _ ≤ M * ∑ x, |realUniformMass L.carrier (x - (s + t)) - realUniformMass L.carrier x| :=
        convolution_indicator_sub_one_le L.carrier_nonempty hsymm g hgsupport hgsum hg (s + t)
      _ ≤ M * eta := mul_le_mul_of_nonneg_left (hTV _ hsum) hM
      _ ≤ 3 * M * eta := by nlinarith [mul_nonneg hM heta]
      _ ≤ delta / 2 := hbudget.trans (min_le_left _ _)
  · intro s hs t ht
    have hsub : s - t ∈ L.ndilate (kappa + kappa) :=
      CyclicBohr.Set.sub_mem_ndilate (hSL hs) (hSL ht)
    have hneg : -(s - t) ∈ L.ndilate (kappa + kappa) :=
      ((L.ndilate (kappa + kappa)).neg_mem_iff _).2 hsub
    exact (centered_correlation_error_le L.carrier_nonempty f hfsupport hfsum hf heta
      (s - t) (hTV _ hsub) (hTV _ hneg)).trans (hbudget.trans (min_le_right _ _))

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentReturnScale
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped NNReal

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

theorem controlledLocalMomentScale_spec (rank : ℕ) {M delta : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 < delta) :
    0 < controlledLocalMomentScale rank M delta ∧
      controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta ≤
        1 / (100 * (2 * max rank 1 : ℕ) : ℝ≥0) ∧
      1200 * (max rank 1 : ℕ) *
          ((controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta : ℝ≥0) : ℝ) * M ≤
        min (delta / 2) (localMomentGain delta) := by
  have hc : 0 < min (delta / 2) (localMomentGain delta) :=
    lt_min (by positivity) (localMomentGain_pos delta)
  obtain ⟨hr, hsmall, herror⟩ := localizedAverageScale_spec rank hM
    (show 0 < min (delta / 2) (localMomentGain delta) / 3 by positivity)
  have heq : controlledLocalMomentScale rank M delta + controlledLocalMomentScale rank M delta =
      localizedAverageScale rank M (min (delta / 2) (localMomentGain delta) / 3) := by
    unfold controlledLocalMomentScale
    ring
  refine ⟨div_pos hr (by norm_num), ?_, ?_⟩
  · rwa [heq]
  · rw [heq]
    nlinarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem normalized_local_alternatives_at_scale
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (S : Finset (ZMod N)) (hS : S.Nonempty)
    (f g : ZMod N → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    (hgsupport : ∀ x, x ∉ L.carrier → g x = 0)
    {u v M delta : ℝ} (hu : 0 < u) (hv : 0 < v) (hM : 0 ≤ M) (hdelta : 0 < delta)
    (hmeanf : (𝔼 x ∈ L.carrier, f x) = u) (hmeang : (𝔼 x ∈ L.carrier, g x) = v)
    (hcapf : ∀ x, f x / u ≤ M) (hcapg : ∀ x, g x / v ≤ M)
    (hSL : S ⊆ (L.ndilate (controlledLocalMomentScale L.rank M delta)).carrier)
    (m : ℕ) (hm : 0 < m) :
    sumLp S (fun x => convolution L.carrier (fun y => f y / u) (fun y => g y / v) x - 1)
        (2 * m) ≤ delta ∨
      ∃ h : ZMod N → ℝ, (h = (fun x => f x / u) ∨ h = (fun x => g x / v)) ∧
        ∃ m' : ℕ, 0 < m' ∧ m ≤ m' ∧ m' ≤ localMomentExponentFactor delta * m ∧
          1 + localMomentGain delta ≤ differenceLp S (correlation L.carrier h h) (2 * m') := by
  have hfnorm := normalized_mass_one L.carrier f hfsupport hu hmeanf
  have hgnorm := normalized_mass_one L.carrier g hgsupport hv hmeang
  have hcard : (L.carrier.card : ℝ) ≠ 0 := by exact_mod_cast L.card_pos.ne'
  have hfsum : (∑ x, f x / u) = L.carrier.card := by
    simpa only [one_mul] using (div_eq_iff hcard).mp hfnorm
  have hgsum : (∑ x, g x / v) = L.carrier.card := by
    simpa only [one_mul] using (div_eq_iff hcard).mp hgnorm
  obtain ⟨_, hsmall, herror⟩ := controlledLocalMomentScale_spec L.rank hM hdelta
  apply local_alternatives_of_regular_bohr L hL S hS hSL hsmall
    (fun x => f x / u) (fun x => g x / v) _ _ hfsum hgsum _ _ hdelta herror hm
  · intro x hx
    rw [hfsupport x hx, zero_div]
  · intro x hx
    rw [hgsupport x hx, zero_div]
  · intro x
    exact (abs_of_nonneg (div_nonneg (hf x) hu.le)).le.trans (hcapf x)
  · intro x
    exact (abs_of_nonneg (div_nonneg (hg x) hv.le)).le.trans (hcapg x)

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

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

end Erdos3

end

section

namespace Erdos3

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

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

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

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem capped_center_alternatives
    (B₀ L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (A B F G : ZMod N → ℝ) (origin x y : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    {U V M K c₀ : ℝ} (hU : 0 < U) (hV : 0 < V) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hlowerF : c₀ * U ≤ cellAverage L.carrier F x)
    (hlowerG : c₀ * V ≤ cellAverage L.carrier G y)
    (hparentF : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier F z ≤ K * U)
    (hparentG : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      ∀ z, cellAverage C.carrier G z ≤ K * V)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMU : 1 ≤ M * (c₀ * U)) (hMV : 1 ≤ M * (c₀ * V))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m')) :
    let a := fun r => A (origin + r) - (1 + epsilon) * B (origin + r)
    centerMatchedIntegral L.carrier S.carrier a F G (x, y) ≤
      Real.exp (-(D * p)) * centerPotential L.carrier F G (x, y) ∨
    ∃ C : CyclicBohr.Set N,
      Peeling.admissibleBohrShape B₀ scale extra minimumWidth C ∧
      0 < C.radius ∧ C.radius ≤ 1 ∧
      |centerChildIntegral L.carrier S.carrier a F G (x, y) C.carrier -
        centerMatchedIntegral L.carrier S.carrier a F G (x, y)| ≤ Real.exp (-E) ∧
      centerChildPotential L.carrier S.carrier F G (x, y) C.carrier ≤
        (1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)) * centerPotential L.carrier F G (x, y) := by
  intro a
  have hF0 : ∀ r, 0 ≤ F r := fun r => (hF r).1
  have hG0 : ∀ r, 0 ≤ G r := fun r => (hG r).1
  have hu : 0 < cellAverage L.carrier F x := (mul_pos hc₀ hU).trans_le hlowerF
  have hv : 0 < cellAverage L.carrier G y := (mul_pos hc₀ hV).trans_le hlowerG
  have hf := centerSlice_bounds L.carrier F hF x
  have hg := centerSlice_bounds L.carrier G hG y
  have hfs := centerSlice_supported L.carrier F x
  have hgs := centerSlice_supported L.carrier G y
  have hmf := centerSlice_mean L.carrier F x
  have hmg := centerSlice_mean L.carrier G y
  have hcf := centerSlice_normalized_cap L.carrier F hF x hU hc₀ hM.le hMU hlowerF
  have hcg := centerSlice_normalized_cap L.carrier G hG y hV hc₀ hM.le hMV hlowerG
  rcases normalized_local_alternatives_at_scale L hL S.carrier S.carrier_nonempty
      (centerSlice L.carrier F x) (centerSlice L.carrier G y)
      (fun r => (hf r).1) (fun r => (hg r).1) hfs hgs hu hv hM.le
      (flatComparisonDelta_spec hepsilon).1 hmf hmg hcf hcg hSLmoment m hm with
    hflat | ⟨h, hchoice, m', hm', hmm', hm'upper, hlarge⟩
  · left
    have hflatI := matched_flat_integral_of_niltest_comparison L.carrier S hSreg hSwidth
      A B (centerSlice L.carrier F x) (centerSlice L.carrier G y) (origin + (x + y))
      hu hv (cellAverage_le L.carrier_nonempty F (fun r => (hF r).2) x)
      (cellAverage_le L.carrier_nonempty G (fun r => (hG r).2) y)
      hepsilon hp (by norm_num) hD hR hM.le
      (by simpa only [one_mul] using hMcap) hSlog (by omega) horder hA hB
      (fun r => (hf r).1) (fun r => (hg r).1) hcg hfs hmf hflat hcomplexity hprecision hcompare
    simpa only [centerMatchedIntegral, centerPotential, a, add_assoc] using hflatI
  · right
    obtain ⟨hqp, hsep⟩ := horders m' hmm' hm'upper
    obtain ⟨C, hparent, _, hCpos, hCwidth, hcontract, hintegral⟩ :=
      exists_parent_unbalanced_independent_refinement B₀ L S hL hSpos hSwidth hSreg hSrank
        hfreq hlocalWidth hSL hkappa hSB hrank hwidth
        F G (centerSlice L.carrier F x) (centerSlice L.carrier G y) x y
        (translated_slice_le L.carrier F hF0 x) (translated_slice_le L.carrier G hG0 y)
        hf hg hfs hgs hU hV hc₀ hK hlowerF hlowerG hmf.le hmg.le hparentF hparentG
        hM (localMomentGain_pos δ) ((localMomentGain_le_half δ).trans (by norm_num)) hp hH
        hMcap hcf hcg herror (2 * m') (by omega) ⟨m', by omega⟩ hqp h hchoice hlarge hsep
        hW hWcap hQ hE
    obtain ⟨_, _, hpotential⟩ := hcontract
    exact ⟨C, hparent, hCpos, hCwidth,
      hintegral (fun r => a (x + y + r)) (fun r => ha (origin + (x + y + r))), hpotential⟩

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

end Erdos3.CellRefinement

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.CellRefinement.capped_center_alternatives := @OAI.Erdos3.CellRefinement.capped_center_alternatives
