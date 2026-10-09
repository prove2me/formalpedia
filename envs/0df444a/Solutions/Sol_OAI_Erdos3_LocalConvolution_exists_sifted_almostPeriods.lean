-- Prove2me | solution 1 for OAI.Erdos3.LocalConvolution.exists_sifted_almostPeriods
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:53:21.055212+00:00
-- url     : https://prove2.me/submissions/b711f80a-199a-475f-9e4b-92f1229d2742

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

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

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

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

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FinitePairProbability
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem good_pair_expect_ge {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (hA : A.Nonempty) (hB : B.Nonempty) (bad : ι → κ → Bool) {epsilon : ℝ}
    (hbad : (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) ≤
      epsilon * (A.card : ℝ) * B.card) :
    1 - epsilon ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, if bad a b then (0 : ℝ) else 1 := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hbadmean : (𝔼 a ∈ A, 𝔼 b ∈ B, if bad a b then (1 : ℝ) else 0) ≤ epsilon := by
    simp_rw [Finset.expect_eq_sum_div_card]
    rw [← Finset.sum_div, div_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hbad]
  have hpoint (a : ι) (b : κ) : (if bad a b then (0 : ℝ) else 1) =
      1 - (if bad a b then (1 : ℝ) else 0) := by
    cases bad a b <;> norm_num
  simp_rw [hpoint, Finset.expect_sub_distrib, Finset.expect_const hB, Finset.expect_const hA]
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RectangleDensity
namespace OAI

section

namespace Erdos3

theorem rectangle_density_bounds {ι κ : Type*} {A S : Finset ι} {B T : Finset κ}
    (hAS : A ⊆ S) (hBT : B ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    {delta : ℝ} (hdelta : 0 < delta)
    (hprod : delta * (S.card : ℝ) * T.card ≤ (A.card : ℝ) * B.card) :
    A.Nonempty ∧ B.Nonempty ∧
      delta * (S.card : ℝ) ≤ A.card ∧ delta * (T.card : ℝ) ≤ B.card := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hAc : (0 : ℝ) ≤ A.card := by positivity
  have hBc : (0 : ℝ) ≤ B.card := by positivity
  have hASc : (A.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hAS
  have hBTc : (B.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hBT
  have hab : 0 < (A.card : ℝ) * B.card :=
    lt_of_lt_of_le (by positivity) hprod
  have ha : (0 : ℝ) < A.card := (mul_pos_iff.mp hab).resolve_right
    (fun h => (not_lt_of_ge hAc) h.1)
    |>.1
  have hb : (0 : ℝ) < B.card := (mul_pos_iff.mp hab).resolve_right
    (fun h => (not_lt_of_ge hAc) h.1)
    |>.2
  have hleft : delta * (S.card : ℝ) ≤ A.card := by
    apply (mul_le_mul_iff_left₀ hTc).mp
    nlinarith [mul_le_mul_of_nonneg_left hBTc hAc]
  have hright : delta * (T.card : ℝ) ≤ B.card := by
    apply (mul_le_mul_iff_left₀ hSc).mp
    nlinarith [mul_le_mul_of_nonneg_right hASc hBc]
  exact ⟨Finset.card_pos.mp (by exact_mod_cast ha),
    Finset.card_pos.mp (by exact_mod_cast hb), hleft, hright⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LocalWeightedSampling
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem correlation_eq_sum_add (L : Finset G) (f g : G → ℝ) (a b : G) :
    correlation L f g (a - b) = (∑ x, f (x + a) * g (x + b)) / L.card := by
  rw [correlation_sub]
  congr 1
  apply Fintype.sum_equiv (Equiv.neg G)
  intro x
  simp [sub_eq_add_neg, add_comm]

theorem correlation_nonneg (L : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (t : G) :
    0 ≤ correlation L f g t :=
  div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hf _) (hg _))) (by positivity)

theorem expect_local_sample_pair (L U : Finset G) (hL : L.Nonempty) (hU : U.Nonempty)
    (f : G → ℝ) (a b : G) {M : ℝ} (hM : 0 < M)
    (hsupport : ∀ x, x ∉ U → f (x + a) * f (x + b) = 0) :
    (𝔼 x : U, (f ((x : G) + a) / M) * (f ((x : G) + b) / M)) =
      ((L.card : ℝ) / ((U.card : ℝ) * M ^ 2)) * correlation L f f (a - b) := by
  have hLc : (L.card : ℝ) ≠ 0 := by exact_mod_cast hL.card_ne_zero
  have hUc : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.card_ne_zero
  have hsum : (∑ x ∈ U, f (x + a) * f (x + b)) = ∑ x, f (x + a) * f (x + b) := by
    apply Finset.sum_subset (Finset.subset_univ U)
    intro x _ hx
    exact hsupport x hx
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort U (fun x : G => (f (x + a) / M) * (f (x + b) / M)), Fintype.card_coe]
  simp_rw [div_mul_div_comm, ← pow_two]
  rw [← Finset.sum_div, hsum, correlation_eq_sum_add]
  field_simp

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalWeightedSifting
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_subset_sum_ge_weighted {ι : Type*} (S : Finset ι)
    (u f : ι → ℝ) (hu : ∀ a ∈ S, 0 ≤ u a ∧ u a ≤ 1) :
    ∃ A ⊆ S, (∑ a ∈ S, u a * f a) ≤ ∑ a ∈ A, f a := by
  classical
  refine ⟨S.filter (fun a => 0 ≤ f a), Finset.filter_subset _ _, ?_⟩
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hf : 0 ≤ f a
  · simpa only [hf, ite_true, one_mul] using mul_le_mul_of_nonneg_right (hu a ha).2 hf
  · simp only [hf, ite_false]
    exact mul_nonpos_of_nonneg_of_nonpos (hu a ha).1 (le_of_not_ge hf)

theorem exists_rectangle_sum_ge_weighted {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (u : ι → ℝ) (v : κ → ℝ) (w : ι → κ → ℝ)
    (hu : ∀ a ∈ S, 0 ≤ u a ∧ u a ≤ 1)
    (hv : ∀ b ∈ T, 0 ≤ v b ∧ v b ≤ 1) :
    ∃ A ⊆ S, ∃ B ⊆ T,
      (∑ a ∈ S, ∑ b ∈ T, u a * v b * w a b) ≤ ∑ a ∈ A, ∑ b ∈ B, w a b := by
  obtain ⟨A, hAS, hA⟩ := exists_subset_sum_ge_weighted S u
    (fun a => ∑ b ∈ T, v b * w a b) hu
  obtain ⟨B, hBT, hB⟩ := exists_subset_sum_ge_weighted T v
    (fun b => ∑ a ∈ A, w a b) hv
  refine ⟨A, hAS, B, hBT, ?_⟩
  calc
    _ = ∑ a ∈ S, u a * ∑ b ∈ T, v b * w a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ a ∈ A, ∑ b ∈ T, v b * w a b := hA
    _ = ∑ b ∈ T, v b * ∑ a ∈ A, w a b := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ b ∈ B, ∑ a ∈ A, w a b := hB
    _ = _ := Finset.sum_comm

end Erdos3

end

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*}

theorem sampleWeight_bounds (P : Ω → ι → ℝ) {q : ℕ} (t : Fin q → Ω) (a : ι)
    (hP : ∀ x, 0 ≤ P x a ∧ P x a ≤ 1) :
    0 ≤ sampleWeight P t a ∧ sampleWeight P t a ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (hP (t i)).1)
  · exact Finset.prod_le_one (fun i _ => (hP (t i)).1) (fun i _ => (hP (t i)).2)

variable [Fintype Ω]

theorem expect_sampleWeight_mul (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ)
    (q : ℕ) (a : ι) (b : κ) :
    (𝔼 t : Fin q → Ω, sampleWeight P t a * sampleWeight Q t b) =
      (𝔼 x : Ω, P x a * Q x b) ^ q := by
  simpa only [sampleWeight, ← Finset.prod_mul_distrib, Fintype.piFinset_univ] using
    (Finset.expect_pow Finset.univ (fun x => P x a * Q x b) q).symm

theorem expect_sample_score (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ)
    (q : ℕ) (S : Finset ι) (T : Finset κ) (w : ι → κ → ℝ) :
    (𝔼 t : Fin q → Ω, ∑ a ∈ S, ∑ b ∈ T,
      sampleWeight P t a * sampleWeight Q t b * w a b) =
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q * w a b := by
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.expect_mul, expect_sampleWeight_mul]

theorem exists_rectangle_score_ge [Nonempty Ω]
    (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ) (q : ℕ)
    (S : Finset ι) (T : Finset κ) (w : ι → κ → ℝ)
    (hP : ∀ x, ∀ a ∈ S, 0 ≤ P x a ∧ P x a ≤ 1)
    (hQ : ∀ x, ∀ b ∈ T, 0 ≤ Q x b ∧ Q x b ≤ 1) :
    ∃ A ⊆ S, ∃ B ⊆ T,
      (∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q * w a b) ≤
        ∑ a ∈ A, ∑ b ∈ B, w a b := by
  obtain ⟨t, _, ht⟩ := Finset.exists_le_of_le_expect
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin q → Ω)).Nonempty)
    (le_of_eq (expect_sample_score P Q q S T w).symm)
  obtain ⟨A, hAS, B, hBT, hAB⟩ := exists_rectangle_sum_ge_weighted S T
    (sampleWeight P t) (sampleWeight Q t) w
    (fun a ha => sampleWeight_bounds P t a (fun x => hP x a ha))
    (fun b hb => sampleWeight_bounds Q t b (fun x => hQ x b hb))
  exact ⟨A, hAS, B, hBT, ht.trans hAB⟩

end Erdos3.WeightedSifting

end

section

namespace Erdos3.WeightedSifting

open scoped BigOperators

variable {Ω ι κ : Type*} [Fintype Ω] [Nonempty Ω]

theorem exists_dense_rectangle_of_score
    (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ) (q : ℕ)
    (S : Finset ι) (T : Finset κ) (hS : S.Nonempty) (hT : T.Nonempty)
    (bad : ι → κ → Bool)
    (hP : ∀ x, ∀ a ∈ S, 0 ≤ P x a ∧ P x a ≤ 1)
    (hQ : ∀ x, ∀ b ∈ T, 0 ≤ Q x b ∧ Q x b ≤ 1)
    {delta epsilon : ℝ} (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hscore : delta * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q *
        (1 - (if bad a b then 1 else 0) / epsilon)) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      delta * (S.card : ℝ) ≤ A.card ∧ delta * (T.card : ℝ) ≤ B.card ∧
      (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) ≤
        epsilon * (A.card : ℝ) * B.card := by
  obtain ⟨A, hAS, B, hBT, hAB⟩ := exists_rectangle_score_ge P Q q S T
    (fun a b => 1 - (if bad a b then 1 else 0) / epsilon) hP hQ
  have hsum : (∑ a ∈ A, ∑ b ∈ B, (1 - (if bad a b then (1 : ℝ) else 0) / epsilon)) =
      (A.card : ℝ) * B.card -
        (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) / epsilon := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.sum_div]
  have hscoreAB := hscore.trans hAB
  rw [hsum] at hscoreAB
  have hbad0 : 0 ≤ ∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0 := by positivity
  have hprod : delta * (S.card : ℝ) * T.card ≤ (A.card : ℝ) * B.card := by
    linarith [div_nonneg hbad0 hepsilon.le]
  obtain ⟨hA, hB, hAdensity, hBdensity⟩ := rectangle_density_bounds hAS hBT hS hT hdelta hprod
  refine ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, ?_⟩
  have hdiv : (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) / epsilon ≤
      (A.card : ℝ) * B.card := by
    have : 0 ≤ delta * (S.card : ℝ) * T.card := by positivity
    linarith
  have h := (div_le_iff₀ hepsilon).mp hdiv
  nlinarith

theorem exists_dense_rectangle_of_moments
    (P : Ω → ι → ℝ) (Q : Ω → κ → ℝ) (q : ℕ)
    (S : Finset ι) (T : Finset κ) (hS : S.Nonempty) (hT : T.Nonempty)
    (bad : ι → κ → Bool)
    (hP : ∀ x, ∀ a ∈ S, 0 ≤ P x a ∧ P x a ≤ 1)
    (hQ : ∀ x, ∀ b ∈ T, 0 ≤ Q x b ∧ Q x b ≤ 1)
    {mu epsilon : ℝ} (hmu : 0 < mu) (hepsilon : 0 < epsilon)
    (htotal : mu * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : Ω, P x a * Q x b) ^ q)
    (hbad : (∑ a ∈ S, ∑ b ∈ T,
      if bad a b then (𝔼 x : Ω, P x a * Q x b) ^ q else 0) ≤
        epsilon / 2 * mu * (S.card : ℝ) * T.card) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      mu / 2 * (S.card : ℝ) ≤ A.card ∧ mu / 2 * (T.card : ℝ) ≤ B.card ∧
      (∑ a ∈ A, ∑ b ∈ B, if bad a b then (1 : ℝ) else 0) ≤
        epsilon * (A.card : ℝ) * B.card := by
  apply exists_dense_rectangle_of_score P Q q S T hS hT bad hP hQ (by positivity) hepsilon
  have hpoint (a : ι) (b : κ) :
      (𝔼 x : Ω, P x a * Q x b) ^ q * (1 - (if bad a b then 1 else 0) / epsilon) =
        (𝔼 x : Ω, P x a * Q x b) ^ q -
          (if bad a b then (𝔼 x : Ω, P x a * Q x b) ^ q else 0) / epsilon := by
    split_ifs <;> ring
  simp_rw [hpoint, Finset.sum_sub_distrib, ← Finset.sum_div]
  have hbad' : (∑ a ∈ S, ∑ b ∈ T,
      if bad a b then (𝔼 x : Ω, P x a * Q x b) ^ q else 0) / epsilon ≤
        mu / 2 * (S.card : ℝ) * T.card := by
    apply (div_le_iff₀ hepsilon).mpr
    nlinarith [hbad]
  linarith

end Erdos3.WeightedSifting

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem exists_dense_sets_of_correlation_moment
    (L U S T K : Finset G) (hL : L.Nonempty) (hU : U.Nonempty)
    (hS : S.Nonempty) (hT : T.Nonempty) (f : G → ℝ)
    {M alpha threshold epsilon : ℝ} (hM : 0 < M) (halpha : 0 < alpha)
    (hthreshold : 0 ≤ threshold) (hepsilon : 0 < epsilon)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hsupport : ∀ a ∈ S, ∀ b ∈ T, ∀ x, x ∉ U → f (x + a) * f (x + b) = 0)
    (q : ℕ)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S, 𝔼 b ∈ T, correlation L f f (a - b) ^ q)
    (hbad : ∀ a ∈ S, ∀ b ∈ T, a - b ∉ K → correlation L f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      (((L.card : ℝ) / ((U.card : ℝ) * M ^ 2) * alpha) ^ q / 2) * S.card ≤ A.card ∧
      (((L.card : ℝ) / ((U.card : ℝ) * M ^ 2) * alpha) ^ q / 2) * T.card ≤ B.card ∧
      1 - epsilon ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, if a - b ∈ K then (1 : ℝ) else 0 := by
  classical
  let : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  let P : U → G → ℝ := fun x a => f ((x : G) + a) / M
  let beta : ℝ := (L.card : ℝ) / ((U.card : ℝ) * M ^ 2)
  let bad : G → G → Bool := fun a b => decide (a - b ∉ K)
  have hLc : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hTc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hP (x : U) (a : G) : 0 ≤ P x a ∧ P x a ≤ 1 := by
    exact ⟨div_nonneg (hf _).1 hM.le, (div_le_one hM).mpr (hf _).2⟩
  have hkernel (a : G) (ha : a ∈ S) (b : G) (hb : b ∈ T) :
      (𝔼 x : U, P x a * P x b) = beta * correlation L f f (a - b) :=
    expect_local_sample_pair L U hL hU f a b hM (hsupport a ha b hb)
  have hsumcorr : alpha ^ q * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, correlation L f f (a - b) ^ q := by
    simp_rw [Finset.expect_eq_sum_div_card] at hmoment
    rw [← Finset.sum_div, div_div] at hmoment
    have h := (le_div_iff₀ (mul_pos hTc hSc)).mp hmoment
    nlinarith
  have hraw : (∑ a ∈ S, ∑ b ∈ T, (𝔼 x : U, P x a * P x b) ^ q) =
      beta ^ q * ∑ a ∈ S, ∑ b ∈ T, correlation L f f (a - b) ^ q := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hkernel a ha b hb, mul_pow]
  have htotal : (beta * alpha) ^ q * (S.card : ℝ) * T.card ≤
      ∑ a ∈ S, ∑ b ∈ T, (𝔼 x : U, P x a * P x b) ^ q := by
    rw [hraw]
    calc
      _ = beta ^ q * (alpha ^ q * (S.card : ℝ) * T.card) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumcorr (pow_nonneg hbeta.le q)
  have hbadmoment : (∑ a ∈ S, ∑ b ∈ T,
      if bad a b then (𝔼 x : U, P x a * P x b) ^ q else 0) ≤
        epsilon / 2 * (beta * alpha) ^ q * (S.card : ℝ) * T.card := by
    calc
      _ ≤ ∑ _a ∈ S, ∑ _b ∈ T, (beta * threshold) ^ q := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        by_cases h : bad a b
        · simp only [h, ite_true]
          have hnot : a - b ∉ K := by simpa [bad] using h
          rw [hkernel a ha b hb]
          exact pow_le_pow_left₀
            (mul_nonneg hbeta.le (correlation_nonneg L f f (fun x => (hf x).1) (fun x => (hf x).1) _))
            (mul_le_mul_of_nonneg_left (hbad a ha b hb hnot) hbeta.le) q
        · simp only [h]
          exact pow_nonneg (mul_nonneg hbeta.le hthreshold) q
      _ = beta ^ q * threshold ^ q * (S.card : ℝ) * T.card := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_pow]
        ring
      _ ≤ beta ^ q * (epsilon / 2 * alpha ^ q) * (S.card : ℝ) * T.card :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hseparation (pow_nonneg hbeta.le q)) hSc.le) hTc.le
      _ = _ := by rw [mul_pow]; ring
  obtain ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, hbadAB⟩ :=
    WeightedSifting.exists_dense_rectangle_of_moments P P q S T hS hT bad
      (fun x a _ => hP x a) (fun x b _ => hP x b)
      (pow_pos (mul_pos hbeta halpha) q) hepsilon htotal hbadmoment
  refine ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, ?_⟩
  have hprob := good_pair_expect_ge A B hA hB bad hbadAB
  simpa [bad] using hprob

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open _root_.Finset
open scoped BigOperators

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end

end Erdos3

end

section

open _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {N : ℕ} [NeZero N]

end

end Erdos3

end

section

open AddChar _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

variable {N : ℕ} [NeZero N]

end

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_dense_sets_of_bohr_correlation_moment
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular) (S T K : Finset (ZMod N))
    (hS : S.Nonempty) (hT : T.Nonempty) {kappa : ℝ≥0}
    (hSL : S ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M alpha threshold epsilon : ℝ} (hM : 0 < M) (halpha : 0 < alpha)
    (hthreshold : 0 ≤ threshold) (hepsilon : 0 < epsilon)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (q : ℕ)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S, 𝔼 b ∈ T, correlation L.carrier f f (a - b) ^ q)
    (hbad : ∀ a ∈ S, ∀ b ∈ T, a - b ∉ K → correlation L.carrier f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q) :
    ∃ A ⊆ S, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      ((alpha / (2 * M ^ 2)) ^ q / 2) * S.card ≤ A.card ∧
      ((alpha / (2 * M ^ 2)) ^ q / 2) * T.card ≤ B.card ∧
      1 - epsilon ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, if a - b ∈ K then (1 : ℝ) else 0 := by
  let U := (L.ndilate (1 + kappa)).carrier
  have hU : U.Nonempty := (L.ndilate (1 + kappa)).carrier_nonempty
  have hUcard : U.card ≤ 2 * L.carrier.card := by
    simpa only [Nat.cast_one, one_mul] using
      Erdos3.card_dilate_one_add_le_two_mul hL 1 (by simpa only [Nat.cast_one, one_mul] using hkappa)
  have hsupport : ∀ a ∈ S, ∀ b ∈ T, ∀ x, x ∉ U → f (x + a) * f (x + b) = 0 := by
    intro a ha b _ x hx
    have hxa : x + a ∉ L.carrier := by
      intro h
      have h₁ : x + a ∈ L.ndilate (1 : ℝ≥0) := by
        simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
          CyclicBohr.Set.mem_carrier] using h
      have h₂ := CyclicBohr.Set.sub_mem_ndilate h₁ (hSL ha)
      exact hx (by simpa only [U, add_sub_cancel_right, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using h₂)
    rw [hfsupport _ hxa, zero_mul]
  obtain ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, hprob⟩ :=
    exists_dense_sets_of_correlation_moment L.carrier U S T K L.carrier_nonempty hU hS hT
      f hM halpha hthreshold hepsilon hf hsupport q hmoment hbad hseparation
  have hLc : (0 : ℝ) < L.carrier.card := by exact_mod_cast L.card_pos
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hUcardR : (U.card : ℝ) ≤ 2 * L.carrier.card := by exact_mod_cast hUcard
  have hratio : 1 / (2 * M ^ 2) ≤ (L.carrier.card : ℝ) / ((U.card : ℝ) * M ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hUcardR (sq_nonneg M)]
  have hbase : alpha / (2 * M ^ 2) ≤
      (L.carrier.card : ℝ) / ((U.card : ℝ) * M ^ 2) * alpha := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      mul_le_mul_of_nonneg_right hratio halpha.le
  have hdensity := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ alpha / (2 * M ^ 2)) hbase q)
    (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨A, hAS, B, hBT, hA, hB,
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg S.card)).trans hAdensity,
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg T.card)).trans hBdensity, hprob⟩

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem card_add_le_two_mul_of_small_bohr
    (B : Set N) (hBreg : B.IsRankRegular) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {A S : Finset (ZMod N)} (z : ZMod N)
    (hA : ∀ a ∈ A, a - z ∈ B.carrier) (hS : S ⊆ (B.ndilate kappa).carrier) :
    (A + S).card ≤ 2 * B.carrier.card := by
  have hsub : A + S ⊆ (B.ndilate (1 + kappa)).carrier.image (fun x => z + x) := by
    intro x hx
    obtain ⟨a, ha, s, hs, rfl⟩ := Finset.mem_add.mp hx
    have haB : a - z ∈ B.ndilate (1 : ℝ≥0) := by
      simpa only [ndilate_one, mem_iff, mem_carrier] using hA a ha
    have hadd := add_mem_ndilate haB (hS hs)
    refine Finset.mem_image.mpr ⟨(a - z) + s, hadd, ?_⟩
    abel
  have houter : (B.ndilate (1 + kappa)).carrier.card ≤ 2 * B.carrier.card := by
    simpa only [Nat.cast_one, one_mul] using
      Erdos3.card_dilate_one_add_le_two_mul hBreg 1 (by simpa only [Nat.cast_one, one_mul] using hkappa)
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans houter)

theorem initialSamplingScale_pos (B : Set N) : 0 < B.initialSamplingScale := by
  unfold initialSamplingScale
  positivity

theorem initialSamplingScale_le_one (B : Set N) : B.initialSamplingScale ≤ 1 := by
  unfold initialSamplingScale
  rw [div_le_one (by positivity)]
  exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)

theorem exists_initial_regular_sampling_bohr
    (B : Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular) :
    ∃ C : Set N, C.frequencies = B.frequencies ∧ C.IsRankRegular ∧
      (B.initialSamplingScale : ℝ) * B.radius / 2 ≤ C.radius ∧
      C.radius ≤ B.initialSamplingScale * B.radius ∧ C.carrier ⊆ B.carrier ∧
      ∀ (A : Finset (ZMod N)) (z : ZMod N),
        (∀ a ∈ A, a - z ∈ B.carrier) → (A + C.carrier).card ≤ 2 * B.carrier.card := by
  obtain ⟨C, hfreq, hreg, hlo, hhi, hsub, _⟩ :=
    exists_controlled_regular_subdilate B hBpos B.initialSamplingScale
      B.initialSamplingScale_pos B.initialSamplingScale_le_one
  have hCB : C.carrier ⊆ B.carrier := by
    apply hsub.trans
    simpa only [ndilate_one] using
      carrier_ndilate_mono (B := B) B.initialSamplingScale_le_one
  refine ⟨C, hfreq, hreg, hlo, hhi, hCB, ?_⟩
  intro A z hA
  exact card_add_le_two_mul_of_small_bohr B hBreg le_rfl z hA hsub

theorem sumset_le_exp_of_relative_density
    (B : Set N) {A S : Finset (ZMod N)} {p : ℝ}
    (hsum : (A + S).card ≤ 2 * B.carrier.card)
    (hdensity : Real.exp (-p) * B.carrier.card ≤ A.card) :
    ((A + S).card : ℝ) ≤ (2 * Real.exp p) * A.card := by
  have hsize : (B.carrier.card : ℝ) ≤ Real.exp p * A.card := by
    calc
      (B.carrier.card : ℝ) = Real.exp p * (Real.exp (-p) * B.carrier.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A.card :=
        mul_le_mul_of_nonneg_left hdensity (Real.exp_pos p).le
  have hsumR : ((A + S).card : ℝ) ≤ 2 * B.carrier.card := by exact_mod_cast hsum
  nlinarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped Pointwise NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DifferenceEventProbability
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem smoothedDifferenceEventProbability_sub_le
    (A₁ A₂ K : Finset (ZMod N)) {R : Finset (ZMod N)} (hR : R.Nonempty) {epsilon : ℝ}
    (hshift : ∀ t ∈ R,
      |differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0| ≤ epsilon) :
    |smoothedDifferenceEventProbability A₁ A₂ K R - differenceEventProbability A₁ A₂ K 0| ≤
      epsilon := by
  have heq : smoothedDifferenceEventProbability A₁ A₂ K R - differenceEventProbability A₁ A₂ K 0 =
      𝔼 t ∈ R, (differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const hR]
    rfl
  rw [heq]
  have hnorm := RCLike.norm_expect_le (K := ℝ)
    (f := fun t => differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0)
    (s := R)
  calc
    _ ≤ 𝔼 t ∈ R, |differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ 𝔼 _t ∈ R, epsilon := Finset.expect_le_expect hshift
    _ = epsilon := Finset.expect_const hR epsilon

theorem differenceEventProbability_smoothing_of_triple_shifts
    (A₁ A₂ K : Finset (ZMod N)) {R : Finset (ZMod N)} (hR : R.Nonempty) {epsilon : ℝ}
    (hshift : ∀ t ∈ R, ∀ x,
      |setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) (x + t) -
        setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) x| ≤ epsilon) :
    |smoothedDifferenceEventProbability A₁ A₂ K R - differenceEventProbability A₁ A₂ K 0| ≤
      epsilon := by
  apply smoothedDifferenceEventProbability_sub_le A₁ A₂ K hR
  intro t ht
  simpa only [differenceEventProbability_eq_triple, zero_add] using hshift t ht 0

end Erdos3.CyclicCrootSisask

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SiftingDensityBudget
namespace OAI

section

namespace Erdos3.LocalConvolution

theorem sifting_density_ge_exp {M alpha p : ℝ} (hM : 0 < M) (halpha : 1 ≤ alpha)
    (hp : 1 ≤ p) (hcap : M ≤ Real.exp p) (q : ℕ) :
    Real.exp (-(3 * (q : ℝ) * p + 1)) ≤ (alpha / (2 * M ^ 2)) ^ q / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have htwoP : (2 : ℝ) ≤ Real.exp p := htwo.trans (Real.exp_le_exp.mpr hp)
  have hden : 2 * M ^ 2 ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * (Real.exp p) ^ 2 :=
        mul_le_mul htwoP (pow_le_pow_left₀ hM.le hcap 2) (sq_nonneg M) (Real.exp_nonneg p)
      _ = _ := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hbase : Real.exp (-3 * p) ≤ alpha / (2 * M ^ 2) := by
    calc
      _ = 1 / Real.exp (3 * p) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
      _ ≤ 1 / (2 * M ^ 2) := one_div_le_one_div_of_le (by positivity) hden
      _ ≤ _ := div_le_div_of_nonneg_right halpha (by positivity)
  have hhalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) htwo
  have hpow : (Real.exp (-3 * p)) ^ q = Real.exp (-3 * (q : ℝ) * p) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = (Real.exp (-3 * p)) ^ q * Real.exp (-1) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      ring
    _ ≤ (alpha / (2 * M ^ 2)) ^ q * (1 / 2) :=
      mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) hbase q) hhalf
        (Real.exp_nonneg _) (pow_nonneg (div_nonneg (by linarith) (by positivity)) q)
    _ = _ := by ring

theorem sifting_density_ge_exp_quadratic {M alpha p C : ℝ}
    (hM : 0 < M) (halpha : 1 ≤ alpha) (hp : 1 ≤ p) (hcap : M ≤ Real.exp p)
    (q : ℕ) (hq : (q : ℝ) ≤ C * p) :
    Real.exp (-((3 * C + 1) * p ^ 2)) ≤ (alpha / (2 * M ^ 2)) ^ q / 2 := by
  have hp0 : 0 ≤ p := by linarith
  have hcost : 3 * (q : ℝ) * p + 1 ≤ (3 * C + 1) * p ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hq hp0]
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (sifting_density_ge_exp hM halpha hp hcap q)

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open RelativeChangSanders
open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_difference_event_almostPeriods_with_width
    (S B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBwidth : B.radius ≤ 1)
    (hBreg : B.IsRankRegular) (hBrank : 1 ≤ B.rank)
    (A₁ A₂ K : Finset (ZMod N)) (z : ZMod N)
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 1 ≤ p)
    (hA₂B : ∀ a ∈ A₂, a - z ∈ B.carrier)
    (hdensity₁ : Real.exp (-p) * S.carrier.card ≤ A₁.card)
    (hdensity₂ : Real.exp (-p) * B.carrier.card ≤ A₂.card)
    (hK : K.card ≤ 2 * S.carrier.card) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      R.carrier ⊆ B.carrier ∧
      (R.rank : ℝ) ≤ B.rank + almostPeriodicityWidthConstant epsilon * (1 + p) ^ 4 ∧
      B.radius * Real.exp (-(almostPeriodicityWidthConstant epsilon *
        (1 + p + Real.log (2 + B.rank)))) ≤ R.radius ∧
      |smoothedDifferenceEventProbability A₁ A₂ K R.carrier - differenceEventProbability A₁ A₂ K 0| ≤
        epsilon := by
  have hp0 : 0 ≤ p := by linarith
  have hA₁pos : (0 : ℝ) < A₁.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast S.card_pos)).trans_le hdensity₁
  have hA₂pos : (0 : ℝ) < A₂.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast B.card_pos)).trans_le hdensity₂
  have hA₁ : A₁.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA₁pos)
  have hA₂ : A₂.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA₂pos)
  have hSsize : (S.carrier.card : ℝ) ≤ Real.exp p * A₁.card := by
    calc
      (S.carrier.card : ℝ) = Real.exp p * (Real.exp (-p) * S.carrier.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A₁.card :=
        mul_le_mul_of_nonneg_left hdensity₁ (Real.exp_pos p).le
  have htwo : 2 ≤ Real.exp p := Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr hp)
  have hratio : (K.card : ℝ) / (-A₁).card ≤ Real.exp (2 * p) := by
    rw [Finset.card_neg, div_le_iff₀ hA₁pos]
    calc
      (K.card : ℝ) ≤ 2 * S.carrier.card := by exact_mod_cast hK
      _ ≤ 2 * (Real.exp p * A₁.card) := mul_le_mul_of_nonneg_left hSsize (by norm_num)
      _ ≤ Real.exp p * (Real.exp p * A₁.card) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (2 * p) * A₁.card := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
  obtain ⟨B₀, hfreq, hB₀reg, hB₀lo, hB₀hi, hB₀B, hsumset⟩ :=
    B.exists_initial_regular_sampling_bohr hBpos hBreg
  have hB₀rank : B₀.rank = B.rank := congrArg Finset.card hfreq
  have hd : (0 : ℝ) < B.rank := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hBrank)
  have hd1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
  have hscale : (B.initialSamplingScale : ℝ) = 1 / (200 * (B.rank : ℝ)) := by
    norm_num [CyclicBohr.Set.initialSamplingScale, max_eq_left hBrank]
    ring
  have hB₀lower : B.radius / (400 * (B.rank : ℝ)) ≤ B₀.radius := by
    rw [hscale] at hB₀lo
    convert hB₀lo using 1
    ring
  have hB₀pos : 0 < B₀.radius := lt_of_lt_of_le (by positivity) hB₀lower
  have hdoubling : ((A₂ + B₀.carrier).card : ℝ) ≤ (2 * Real.exp p) * A₂.card :=
    B.sumset_le_exp_of_relative_density (hsumset A₂ z hA₂B) hdensity₂
  obtain ⟨R, hRreg, hRrank, hRwidth, hRupper, hRB₀, hshift⟩ :=
    exists_quartic_local_almostPeriods B₀ hB₀pos hB₀reg hA₂ hA₁.neg K
      hepsilon hepsilon1 hp0 hratio hdoubling
  let C := rankQuarticFactor epsilon
  let D := C * (p + 1) ^ 4
  have hC : 0 < C := rankQuarticFactor_pos epsilon
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdmax : max B₀.rank 1 = B.rank := by rw [hB₀rank, max_eq_left hBrank]
  let a : ℝ≥0 :=
    (100 * ((2 * max B₀.rank 1 : ℕ) : ℝ≥0) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
  have ha : 1 / (1000 * (B.rank : ℝ) * (D + 1)) ≤ (a : ℝ) := by
    simpa [a, hdmax] using BohrWidthBudget.selector_scale_lower_bound hd hD
  have hRrational : epsilon * Real.exp (-p) * B.radius /
      (10240000000 * (B.rank : ℝ) ^ 3 * (D + 1)) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_lower_bound
      (u := epsilon * Real.exp (-p)) (by positivity) hd1 hD hBpos hBwidth hB₀lower ha
    apply h.trans
    simpa only [a, D, C, hdmax] using hRwidth
  have hRexp : B.radius * Real.exp (-(almostPeriodicityWidthConstant epsilon *
      (1 + p + Real.log (2 + B.rank)))) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_ge_exponential hepsilon hC.le hp0 hd1 B.radius_nonneg
    apply le_trans _ hRrational
    simpa only [almostPeriodicityWidthConstant, C, D] using h
  have hRpos : 0 < R.radius :=
    (mul_pos hBpos (Real.exp_pos _)).trans_le hRexp
  have hRone : R.radius ≤ 1 := by
    apply hRupper.trans
    have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hnum : epsilon * Real.exp (-p) ≤ 1 :=
      (mul_le_mul_of_nonneg_left he hepsilon.le).trans (by simpa using hepsilon1)
    apply (div_le_one (by positivity : 0 < 8 * (D + 1))).mpr
    nlinarith
  have hRrank' : (R.rank : ℝ) ≤ B.rank + almostPeriodicityWidthConstant epsilon * (1 + p) ^ 4 := by
    have hconst := rankQuarticFactor_le_widthConstant hepsilon hepsilon1
    rw [hB₀rank] at hRrank
    apply hRrank.trans
    rw [add_comm 1 p]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hconst (by positivity))
  refine ⟨R, hRreg, hRpos, hRone, hRB₀.trans hB₀B, hRrank', hRexp, ?_⟩
  exact differenceEventProbability_smoothing_of_triple_shifts A₁ A₂ K R.carrier_nonempty hshift

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_sifted_almostPeriods
    (L S B₀ : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hBpos : 0 < B₀.radius) (hBwidth : B₀.radius ≤ 1)
    (hBreg : B₀.IsRankRegular) (hBrank : 1 ≤ B₀.rank)
    (T K : Finset (ZMod N)) (hT : T.Nonempty) (z : ZMod N)
    (hTcard : T.card = B₀.carrier.card) (hTB : ∀ b ∈ T, b - z ∈ B₀.carrier)
    {kappa : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hfsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M alpha threshold epsilon eta p C : ℝ}
    (hM : 0 < M) (halpha : 1 ≤ alpha) (hthreshold : 0 ≤ threshold)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (q : ℕ) (hq : (q : ℝ) ≤ C * p)
    (hmoment : alpha ^ q ≤ 𝔼 a ∈ S.carrier, 𝔼 b ∈ T, correlation L.carrier f f (a - b) ^ q)
    (hbad : ∀ a ∈ S.carrier, ∀ b ∈ T, a - b ∉ K → correlation L.carrier f f (a - b) ≤ threshold)
    (hseparation : threshold ^ q ≤ epsilon / 2 * alpha ^ q)
    (hK : K.card ≤ 2 * S.carrier.card) :
    let D := (3 * C + 1) * p ^ 2
    ∃ A ⊆ S.carrier, ∃ B ⊆ T, A.Nonempty ∧ B.Nonempty ∧
      Real.exp (-D) * S.carrier.card ≤ A.card ∧
      Real.exp (-D) * B₀.carrier.card ≤ B.card ∧
      ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
        R.carrier ⊆ B₀.carrier ∧
        (R.rank : ℝ) ≤ B₀.rank + almostPeriodicityWidthConstant eta * (1 + D) ^ 4 ∧
        B₀.radius * Real.exp (-(almostPeriodicityWidthConstant eta *
          (1 + D + Real.log (2 + B₀.rank)))) ≤ R.radius ∧
        1 - epsilon - eta ≤ smoothedDifferenceEventProbability A B K R.carrier := by
  intro D
  obtain ⟨A, hAS, B, hBT, hA, hB, hAdensity, hBdensity, hprob⟩ :=
    exists_dense_sets_of_bohr_correlation_moment L hL S.carrier T K S.carrier_nonempty hT
      hSL hkappa f hfsupport hM (by linarith) hthreshold hepsilon hf q hmoment hbad hseparation
  have hdensity := sifting_density_ge_exp_quadratic hM halpha hp hcap q hq
  have hAd : Real.exp (-D) * S.carrier.card ≤ A.card :=
    (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg S.carrier.card)).trans hAdensity
  have hBd : Real.exp (-D) * B₀.carrier.card ≤ B.card := by
    rw [← hTcard]
    exact (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg T.card)).trans hBdensity
  have hD : 1 ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg hC (sq_nonneg p)]
  obtain ⟨R, hRreg, hRpos, hRwidth, hRB, hRrank, hRlower, hRprob⟩ :=
    exists_difference_event_almostPeriods_with_width S B₀ hBpos hBwidth hBreg hBrank
      A B K z heta heta1 hD (fun b hb => hTB b (hBT hb)) hAd hBd hK
  refine ⟨A, hAS, B, hBT, hA, hB, hAd, hBd, R, hRreg, hRpos, hRwidth,
    hRB, hRrank, hRlower, ?_⟩
  have hprob₀ : 1 - epsilon ≤ differenceEventProbability A B K 0 := by
    simpa only [differenceEventProbability, realSetIndicator, add_zero] using hprob
  have hshift := (abs_le.mp hRprob).1
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.LocalConvolution.exists_sifted_almostPeriods := @OAI.Erdos3.LocalConvolution.exists_sifted_almostPeriods
