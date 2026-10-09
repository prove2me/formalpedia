-- Prove2me | solution 1 for OAI.Erdos3.LocalConvolution.exists_unbalanced_bohr_second_moment_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:44:07.936985+00:00
-- url     : https://prove2.me/submissions/fb62a7d8-7749-4f32-b199-5fc082553efc

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_LocalConvolution_exists_sifted_almostPeriods

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteShellSum
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_le_local_sum_add_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L U : Finset ι) (hLU : L ⊆ U) (f : ι → ℝ) {M : ℝ}
    (hsupport : ∀ x, x ∉ U → f x = 0) (hf : ∀ x, f x ≤ M) :
    (∑ x, f x) ≤ (∑ x ∈ L, f x) + M * ((U.card : ℝ) - L.card) := by
  have hpoint (x : ι) : f x ≤ (if x ∈ L then f x else 0) +
      M * ((if x ∈ U then 1 else 0) - (if x ∈ L then 1 else 0)) := by
    by_cases hxL : x ∈ L
    · simp [hxL, hLU hxL]
    · by_cases hxU : x ∈ U
      · simpa only [hxL, hxU, ite_false, ite_true, sub_zero, mul_one, zero_add] using hf x
      · simp [hxL, hxU, hsupport x hxU]
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset ι)) => hpoint x)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one] using h

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

theorem differenceLp_pow (S : Finset G) (f : G → ℝ) {p : ℕ} (hp : 0 < p) (heven : Even p) :
    differenceLp S f p ^ p = differenceMoment S f p := by
  rw [differenceLp, finiteSetLp_pow _ _ hp, Finset.expect_product]
  simp only [heven.pow_abs, differenceMoment]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

end Erdos3

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

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalCorrelationBounds
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem correlation_self_le_sq (L : Finset G) (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (t : G) : correlation L f f t ≤ M ^ 2 := by
  have hM : 0 ≤ M := (hf 0).1.trans (hf 0).2
  have hcard : (0 : ℝ) < L.card := by exact_mod_cast hL.card_pos
  unfold correlation
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ ∑ x : G, if x ∈ L then M ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ L
      · simp only [hx, ite_true]
        simpa only [pow_two] using mul_le_mul (hf (x + t)).2 (hf x).2 (hf x).1 hM
      · simp [hx, hsupport x hx]
    _ = _ := by simp [mul_comm]

theorem abs_correlation_self_pow_le (L : Finset G) (hL : L.Nonempty) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ L → f x = 0) {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (t : G) (q : ℕ) :
    |correlation L f f t ^ q| ≤ M ^ (2 * q) := by
  have hcorr := correlation_nonneg L f f (fun x => (hf x).1) (fun x => (hf x).1) t
  rw [abs_of_nonneg (pow_nonneg hcorr q), pow_mul]
  exact pow_le_pow_left₀ hcorr (correlation_self_le_sq L hL f hsupport hf t) q

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalCorrelationEnergy
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem correlation_self_le_zero (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L f f t ≤ correlation L f f 0 := by
  have hshift : (∑ x, f (x + t) ^ 2) = ∑ x, f x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
  have hsum : (∑ x, f (x + t) * f x) ≤ ∑ x, f x ^ 2 := by
    have h : (∑ x, 2 * (f (x + t) * f x)) ≤ ∑ x, (f (x + t) ^ 2 + f x ^ 2) :=
      Finset.sum_le_sum (fun x _ => by nlinarith [sq_nonneg (f (x + t) - f x)])
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hshift] at h
    linarith
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L.card : (0 : ℝ) ≤ L.card)
  simpa only [correlation, add_zero, pow_two] using h

theorem correlation_average (L C : Finset G) (f : G → ℝ) (t : G) :
    correlation L (fun x => 𝔼 c ∈ C, f (x + c)) (fun x => 𝔼 c ∈ C, f (x + c)) t =
      𝔼 c ∈ C, 𝔼 d ∈ C, correlation L f f (t + c - d) := by
  change ((∑ x, (𝔼 c ∈ C, f ((x + t) + c)) * (𝔼 d ∈ C, f (x + d))) / L.card) = _
  simp_rw [Finset.expect_mul_expect, ← Finset.expect_sum_comm, Finset.expect_div]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro d _
  rw [correlation_eq_sum_add]
  simp only [add_assoc]

theorem opposite_average_correlation_le_square_mean (L C : Finset G) (f : G → ℝ) (t : G) :
    (𝔼 c ∈ C, 𝔼 d ∈ C, correlation L f f (t + c - d)) ≤
      (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.card := by
  rw [← correlation_average]
  have h := correlation_self_le_zero L (fun x => 𝔼 c ∈ C, f (x + c)) t
  simpa only [correlation, add_zero, pow_two] using h

end Erdos3.LocalConvolution

end

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

variable [DecidableEq G]

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem sum_uniformMass_mul_eq_expect (S : Finset G) (f : G → ℝ) :
    (∑ x, realUniformMass S x * f x) = 𝔼 x ∈ S, f x := by
  rw [Finset.expect_eq_sum_div_card]
  simp only [realUniformMass, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

variable [AddCommGroup G]

theorem expect_add_eq_shift_mass (S : Finset G) (f : G → ℝ) (t : G) :
    (𝔼 x ∈ S, f (x + t)) = ∑ x, realUniformMass S (x - t) * f x := by
  rw [← sum_uniformMass_mul_eq_expect]
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro x
  simp

theorem abs_expect_add_sub_le (S : Finset G) (f : G → ℝ) (t : G)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) :
    |(𝔼 x ∈ S, f (x + t)) - 𝔼 x ∈ S, f x| ≤
      M * ∑ x, |realUniformMass S (x - t) - realUniformMass S x| := by
  rw [expect_add_eq_shift_mass, ← sum_uniformMass_mul_eq_expect]
  exact abs_sum_mul_sub_le _ _ f hf

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

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

theorem smoothed_correlation_le_square_mean
    (L R C : Finset G) (hL : L.Nonempty) (hR : R.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M eta : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hTV : ∀ c ∈ C, ∀ d ∈ C,
      (∑ x, |realUniformMass R (x - (c - d)) - realUniformMass R x|) ≤ eta)
    (z : G) :
    (𝔼 t ∈ R, correlation L f f (z + t)) ≤
      (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.card + M ^ 2 * eta := by
  have hbound (x : G) : |correlation L f f x| ≤ M ^ 2 := by
    simpa only [pow_one, Nat.mul_one] using abs_correlation_self_pow_le L hL f hsupport hf x 1
  have hshift (c : G) (hc : c ∈ C) (d : G) (hd : d ∈ C) :
      (𝔼 t ∈ R, correlation L f f (z + t)) - M ^ 2 * eta ≤
        𝔼 t ∈ R, correlation L f f (z + t + c - d) := by
    have h := (abs_expect_add_sub_le R (fun t => correlation L f f (z + t)) (c - d)
      (fun t => hbound (z + t))).trans (mul_le_mul_of_nonneg_left (hTV c hc d hd) (sq_nonneg M))
    have hlower := (abs_le.mp h).1
    have hindex (t : G) : z + (t + (c - d)) = z + t + c - d := by abel
    simp_rw [hindex] at hlower
    linarith
  have havg := Finset.expect_le_expect (fun c (hc : c ∈ C) =>
    Finset.expect_le_expect (fun d (hd : d ∈ C) => hshift c hc d hd))
  simp only [Finset.expect_const hC] at havg
  have hreorder :
      (𝔼 c ∈ C, 𝔼 d ∈ C, 𝔼 t ∈ R, correlation L f f (z + t + c - d)) =
        𝔼 t ∈ R, 𝔼 c ∈ C, 𝔼 d ∈ C, correlation L f f (z + t + c - d) := by
    calc
      _ = 𝔼 c ∈ C, 𝔼 t ∈ R, 𝔼 d ∈ C, correlation L f f (z + t + c - d) := by
        apply Finset.expect_congr rfl
        intro c _
        exact Finset.expect_comm C R _
      _ = _ := Finset.expect_comm C R _
  rw [hreorder] at havg
  have henergy := Finset.expect_le_expect (fun t (_ : t ∈ R) =>
    opposite_average_correlation_le_square_mean L C f (z + t))
  rw [Finset.expect_const hR] at henergy
  linarith

theorem triple_smoothed_correlation_le_square_mean
    (L A B R C : Finset G) (hL : L.Nonempty) (hA : A.Nonempty) (hB : B.Nonempty)
    (hR : R.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M eta : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hTV : ∀ c ∈ C, ∀ d ∈ C,
      (∑ x, |realUniformMass R (x - (c - d)) - realUniformMass R x|) ≤ eta) :
    (𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R, correlation L f f (a - b + t)) ≤
      (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.card + M ^ 2 * eta := by
  have h := Finset.expect_le_expect (fun a (_ : a ∈ A) =>
    Finset.expect_le_expect (fun b (_ : b ∈ B) =>
      smoothed_correlation_le_square_mean L R C hL hR hC f hsupport hf hTV (a - b)))
  simpa only [Finset.expect_const hA, Finset.expect_const hB] using h

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

theorem localizedAverageScale_le_one (rank : ℕ) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    localizedAverageScale rank R epsilon ≤ 1 := by
  apply (localizedAverageScale_spec rank hR hepsilon).2.1.trans
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast (show 1 ≤ 100 * (2 * max rank 1) by omega)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedLocalAverage
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

theorem exists_translated_local_average
    (S T : Finset G) (hS : S.Nonempty) (hT : T.Nonempty) (f : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (hf : ∀ x, |f x| ≤ M)
    (hTV : ∀ t ∈ T, (∑ x, |realUniformMass S (x - t) - realUniformMass S x|) ≤ eta) :
    ∃ b ∈ S, (𝔼 a ∈ S, 𝔼 x ∈ S, f (a - x)) - M * eta ≤
      𝔼 a ∈ S, 𝔼 t ∈ T, f (a - (b + t)) := by
  have hsingle (a t : G) (ht : t ∈ T) :
      (𝔼 b ∈ S, f (a - b)) - M * eta ≤ 𝔼 b ∈ S, f (a - (b + t)) := by
    have h := (abs_expect_add_sub_le S (fun b => f (a - b)) t
      (fun b => hf (a - b))).trans (mul_le_mul_of_nonneg_left (hTV t ht) hM)
    have hlower := (abs_le.mp h).1
    linarith
  have hlocal (t : G) (ht : t ∈ T) :
      (𝔼 a ∈ S, 𝔼 b ∈ S, f (a - b)) - M * eta ≤
        𝔼 a ∈ S, 𝔼 b ∈ S, f (a - (b + t)) := by
    have h := Finset.expect_le_expect (fun a (_ : a ∈ S) => hsingle a t ht)
    simpa only [Finset.expect_sub_distrib, Finset.expect_const hS] using h
  have hglobal := Finset.expect_le_expect hlocal
  rw [Finset.expect_const hT] at hglobal
  have hreorder : (𝔼 t ∈ T, 𝔼 a ∈ S, 𝔼 b ∈ S, f (a - (b + t))) =
      𝔼 b ∈ S, 𝔼 a ∈ S, 𝔼 t ∈ T, f (a - (b + t)) := by
    calc
      _ = 𝔼 a ∈ S, 𝔼 b ∈ S, 𝔼 t ∈ T, f (a - (b + t)) := by
        rw [Finset.expect_comm T S]
        apply Finset.expect_congr rfl
        intro a _
        exact Finset.expect_comm T S _
      _ = _ := Finset.expect_comm S S _
  exact Finset.exists_le_of_le_expect hS (hglobal.trans_eq hreorder)

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

end Erdos3

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

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem square_mean_le_local_add_boundary
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (C : Finset (ZMod N)) (hC : C.Nonempty) {kappa : ℝ≥0}
    (hCL : C ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.carrier.card ≤
      (𝔼 x ∈ L.carrier, (𝔼 c ∈ C, f (x + c)) ^ 2) +
        200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 := by
  let g : ZMod N → ℝ := fun x => 𝔼 c ∈ C, f (x + c)
  let U := (L.ndilate (1 + kappa)).carrier
  have hLc : (0 : ℝ) < L.carrier.card := by exact_mod_cast L.card_pos
  have hg (x : ZMod N) : 0 ≤ g x ∧ g x ≤ M := by
    constructor
    · exact Finset.expect_nonneg (fun c _ => (hf (x + c)).1)
    · exact (Finset.expect_le_expect (fun c (_ : c ∈ C) => (hf (x + c)).2)).trans_eq
        (Finset.expect_const hC M)
  have hgU : ∀ x, x ∉ U → g x = 0 := by
    intro x hx
    apply Finset.expect_eq_zero
    intro c hc
    apply hsupport
    intro hxc
    have h₁ : x + c ∈ L.ndilate (1 : ℝ≥0) := by
      simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using hxc
    have h₂ := CyclicBohr.Set.sub_mem_ndilate h₁ (hCL hc)
    exact hx (by simpa only [U, add_sub_cancel_right, CyclicBohr.Set.mem_iff,
      CyclicBohr.Set.mem_carrier] using h₂)
  have hLU : L.carrier ⊆ U := by
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := L) (show (1 : ℝ≥0) ≤ 1 + kappa from le_self_add)
  have hshell : (U.card : ℝ) - L.carrier.card ≤
      (200 * (max L.rank 1 : ℕ) * (kappa : ℝ)) * L.carrier.card := by
    have h := (hL kappa hkappa).2
    change ((L.ndilate (1 + kappa)).carrier.card : ℝ) - L.carrier.card ≤ _
    push_cast at h ⊢
    nlinarith
  have hsum := sum_le_local_sum_add_shell L.carrier U hLU (fun x => g x ^ 2)
    (fun x hx => by rw [hgU x hx]; norm_num)
    (fun x => pow_le_pow_left₀ (hg x).1 (hg x).2 2)
  have herror : M ^ 2 * (((U.card : ℝ) - L.carrier.card) / L.carrier.card) ≤
      200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hLc).mpr hshell) (sq_nonneg M)
    nlinarith
  change (∑ x, g x ^ 2) / L.carrier.card ≤
    (𝔼 x ∈ L.carrier, g x ^ 2) + 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2
  calc
    _ ≤ ((∑ x ∈ L.carrier, g x ^ 2) + M ^ 2 * ((U.card : ℝ) - L.carrier.card)) /
        L.carrier.card := div_le_div_of_nonneg_right hsum hLc.le
    _ = (𝔼 x ∈ L.carrier, g x ^ 2) +
        M ^ 2 * (((U.card : ℝ) - L.carrier.card) / L.carrier.card) := by
      rw [Finset.expect_eq_sum_div_card, add_div]
      ring
    _ ≤ _ := add_le_add le_rfl herror

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

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrLocalizedAverage
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_localized_difference_average_at_scale (S : Set N)
    (hSpos : 0 < S.radius) (hSreg : S.IsRankRegular) (f : ZMod N → ℝ)
    {R epsilon : ℝ} (hR : 0 ≤ R) (hf : ∀ x, |f x| ≤ R) (hepsilon : 0 < epsilon)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank R epsilon) :
    ∃ C : Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ b ∈ S.carrier, (𝔼 a ∈ S.carrier, 𝔼 x ∈ S.carrier, f (a - x)) - epsilon ≤
        𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, f (a - (b + t)) := by
  obtain ⟨_, hlimit, hbound⟩ := localizedAverageScale_spec S.rank hR hepsilon
  have hkappa := hscale.trans hlimit
  have hscaleR : (kappa : ℝ) ≤ localizedAverageScale S.rank R epsilon := by
    exact_mod_cast hscale
  have herror : R * (400 * (max S.rank 1 : ℕ) * (kappa : ℝ)) ≤ epsilon := by
    apply le_trans _ hbound
    gcongr
  have hkappa1 : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max S.rank 1) by omega)
  obtain ⟨C, hfreq, hreg, hlo, hhi, hsub, _⟩ :=
    S.exists_controlled_regular_subdilate hSpos kappa hkappa0 hkappa1
  have hkappaR : (0 : ℝ) < kappa := by exact_mod_cast hkappa0
  have hCpos : 0 < C.radius := (show 0 < (kappa : ℝ) * S.radius / 2 by positivity).trans_le hlo
  have hTV : ∀ t ∈ C.carrier,
      (∑ x, |realUniformMass S.carrier (x - t) - realUniformMass S.carrier x|) ≤
        400 * (max S.rank 1 : ℕ) * (kappa : ℝ) := by
    intro t ht
    exact uniformMass_translation_le_of_rankRegular hSreg hkappa (hsub ht)
  obtain ⟨b, hb, havg⟩ := exists_translated_local_average S.carrier C.carrier
    S.carrier_nonempty C.carrier_nonempty f hR hf hTV
  refine ⟨C, hfreq, hreg, hCpos, hlo, hhi, hsub, b, hb, ?_⟩
  linarith

end Erdos3.CyclicBohr.Set

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

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped Pointwise NNReal

variable {N : ℕ} [NeZero N]

theorem card_sub_translated_small_le_two_mul
    (S : Set N) (hS : S.IsRankRegular) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (2 * max S.rank 1 : ℕ) : ℝ≥0))
    (C : Finset (ZMod N)) (hC : C ⊆ (S.ndilate kappa).carrier) (z : ZMod N) :
    (S.carrier - C.image (fun t => z + t)).card ≤ 2 * S.carrier.card := by
  have hsub : S.carrier - C.image (fun t => z + t) ⊆
      (S.ndilate (1 + kappa)).carrier.image (fun x => x - z) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    have haS : a ∈ S.ndilate (1 : ℝ≥0) := by
      simpa only [ndilate_one, mem_iff, mem_carrier] using ha
    have hdiff := sub_mem_ndilate haS (hC ht)
    refine Finset.mem_image.mpr ⟨a - t, hdiff, ?_⟩
    abel
  have houter : (S.ndilate (1 + kappa)).carrier.card ≤ 2 * S.carrier.card := by
    simpa only [Nat.cast_one, one_mul] using
      Erdos3.card_dilate_one_add_le_two_mul hS 1 (by simpa only [Nat.cast_one, one_mul] using hkappa)
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans houter)

end Erdos3.CyclicBohr.Set

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedCorrelationMoment
namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_localized_correlation_moment_at_scale
    (L : Finset (ZMod N)) (hL : L.Nonempty)
    (S : CyclicBohr.Set N) (hSpos : 0 < S.radius) (hSreg : S.IsRankRegular)
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M c : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hc : 0 < c)
    (q : ℕ) (hq : 0 < q) (heven : Even q)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L f f) q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    ∃ C : CyclicBohr.Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ b ∈ S.carrier,
        (1 + c / 2) ^ q ≤
          (𝔼 a ∈ S.carrier, 𝔼 y ∈ C.carrier.image (fun t => b + t), correlation L f f (a - y) ^ q) ∧
        (S.carrier - C.carrier.image (fun t => b + t)).card ≤ 2 * S.carrier.card := by
  have hM : 0 ≤ M := (hf 0).1.trans (hf 0).2
  have hR : 0 ≤ M ^ (2 * q) := pow_nonneg hM _
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  have hmoment : (1 + c) ^ q ≤ differenceMoment S.carrier (correlation L f f) q := by
    have h := pow_le_pow_left₀ (show 0 ≤ 1 + c by linarith) hlarge q
    rwa [differenceLp_pow S.carrier (correlation L f f) hq heven] at h
  obtain ⟨C, hfreq, hreg, hCpos, hlo, hhi, hsub, b, hb, havg⟩ :=
    S.exists_localized_difference_average_at_scale hSpos hSreg (fun x => correlation L f f x ^ q)
      hR (fun x => abs_correlation_self_pow_le L hL f hsupport hf x q) hgap kappa hkappa0 hscale
  have hlocalized : (1 + c / 2) ^ q ≤
      𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, correlation L f f (a - (b + t)) ^ q := by
    unfold differenceMoment at hmoment
    linarith
  refine ⟨C, hfreq, hreg, hCpos, hlo, hhi, hsub, b, hb, ?_, ?_⟩
  · have himage :
        (𝔼 a ∈ S.carrier, 𝔼 y ∈ C.carrier.image (fun t => b + t), correlation L f f (a - y) ^ q) =
          𝔼 a ∈ S.carrier, 𝔼 t ∈ C.carrier, correlation L f f (a - (b + t)) ^ q := by
      apply Finset.expect_congr rfl
      intro a _
      exact Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)
    exact hlocalized.trans_eq himage.symm
  · have hkappa := hscale.trans (localizedAverageScale_spec S.rank hR hgap).2.1
    exact S.card_sub_translated_small_le_two_mul hSreg hkappa C.carrier hsub b

end Erdos3.LocalConvolution

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

theorem smoothedDifferenceEventProbability_eq_average
    (A₁ A₂ K R : Finset (ZMod N)) :
    smoothedDifferenceEventProbability A₁ A₂ K R =
      𝔼 a ∈ A₁, 𝔼 b ∈ A₂, 𝔼 t ∈ R, realSetIndicator K (a - b + t) := by
  unfold smoothedDifferenceEventProbability differenceEventProbability
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [Finset.expect_comm]

end Erdos3.CyclicCrootSisask

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

theorem goodDifferenceSet_subset (S T : Finset G) (f : G → ℝ) (threshold : ℝ) :
    goodDifferenceSet S T f threshold ⊆ S - T := Finset.filter_subset _ _

theorem le_of_mem_goodDifferenceSet {S T : Finset G} {f : G → ℝ} {threshold : ℝ} {x : G}
    (hx : x ∈ goodDifferenceSet S T f threshold) : threshold ≤ f x :=
  (Finset.mem_filter.mp hx).2

theorem le_threshold_of_not_mem_goodDifferenceSet
    {S T : Finset G} {f : G → ℝ} {threshold : ℝ} {a b : G}
    (ha : a ∈ S) (hb : b ∈ T) (hnot : a - b ∉ goodDifferenceSet S T f threshold) :
    f (a - b) ≤ threshold := by
  have hmem : a - b ∈ S - T := Finset.mem_sub.mpr ⟨a, ha, b, hb, rfl⟩
  have h : ¬ threshold ≤ f (a - b) := by
    intro hle
    exact hnot (Finset.mem_filter.mpr ⟨hmem, hle⟩)
  exact (lt_of_not_ge h).le

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

theorem smoothed_correlation_ge_of_good_probability
    (L A B K R : Finset (ZMod N)) (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) {threshold : ℝ}
    (hK : ∀ x ∈ K, threshold ≤ correlation L f f x) :
    threshold * smoothedDifferenceEventProbability A B K R ≤
      𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R, correlation L f f (a - b + t) := by
  rw [smoothedDifferenceEventProbability_eq_average]
  simp only [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro a _
  apply Finset.expect_le_expect
  intro b _
  apply Finset.expect_le_expect
  intro t _
  by_cases h : a - b + t ∈ K
  · simpa only [realSetIndicator, h, ite_true, mul_one] using hK _ h
  · simpa only [realSetIndicator, h, ite_false, mul_zero] using correlation_nonneg L f f hf hf _

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CyclicCrootSisask

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

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

theorem exists_smoothing_of_large_correlation_at_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c epsilon eta p H : ℝ}
    (hM : 0 < M) (hc : 0 < c) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hp : 1 ≤ p) (hH : 0 ≤ H)
    (hcap : M ≤ Real.exp p) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ epsilon / 2 * (1 + c / 2) ^ q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.frequencies = S.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (kappa : ℝ) * S.radius / 2 ≤ C.radius ∧ C.radius ≤ kappa * S.radius ∧
      C.carrier ⊆ S.carrier ∧ C.carrier ⊆ (S.ndilate kappa).carrier ∧
      ∃ z ∈ S.carrier, ∃ A ⊆ S.carrier, ∃ B ⊆ C.carrier.image (fun t => z + t),
        A.Nonempty ∧ B.Nonempty ∧
        Real.exp (-D) * S.carrier.card ≤ A.card ∧ Real.exp (-D) * C.carrier.card ≤ B.card ∧
        ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
          R.carrier ⊆ C.carrier ∧
          (R.rank : ℝ) ≤ C.rank + almostPeriodicityWidthConstant eta * (1 + D) ^ 4 ∧
          C.radius * Real.exp (-(almostPeriodicityWidthConstant eta *
            (1 + D + Real.log (2 + C.rank)))) ≤ R.radius ∧
          (1 + c / 4) * (1 - epsilon - eta) ≤
            𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L.carrier f f (a - b + t) := by
  intro D
  obtain ⟨C, hfreq, hCreg, hCpos, hlo, hhi, hsub, z, hz, hmoment, hdiff⟩ :=
    exists_localized_correlation_moment_at_scale L.carrier L.carrier_nonempty S hSpos hSreg
      f hsupport hf hc q hq heven hlarge kappa hkappa0 hscale
  let T := C.carrier.image (fun t => z + t)
  let K := goodDifferenceSet S.carrier T (correlation L.carrier f f) (1 + c / 4)
  have hT : T.Nonempty := C.carrier_nonempty.image _
  have hTcard : T.card = C.carrier.card :=
    Finset.card_image_of_injOn (fun _ _ _ _ h => add_left_cancel h)
  have hTB : ∀ b ∈ T, b - z ∈ C.carrier := by
    intro b hb
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hb
    simpa only [add_sub_cancel_left] using ht
  have hKcard : K.card ≤ 2 * S.carrier.card :=
    (Finset.card_le_card (goodDifferenceSet_subset _ _ _ _)).trans hdiff
  have hKbad : ∀ a ∈ S.carrier, ∀ b ∈ T, a - b ∉ K →
      correlation L.carrier f f (a - b) ≤ 1 + c / 4 := by
    intro a ha b hb hnot
    exact le_threshold_of_not_mem_goodDifferenceSet ha hb hnot
  have hgap : 0 < (1 + c) ^ q - (1 + c / 2) ^ q := by
    have h := pow_lt_pow_left₀ (show 1 + c / 2 < 1 + c by linarith)
      (show 0 ≤ 1 + c / 2 by linarith) hq.ne'
    linarith
  have hkappa := hscale.trans (localizedAverageScale_spec S.rank (pow_nonneg hM.le (2 * q)) hgap).2.1
  have hkappa1 : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max S.rank 1) by omega)
  have hkappa1R : (kappa : ℝ) ≤ 1 := by exact_mod_cast hkappa1
  have hCwidth : C.radius ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hkappa1R S.radius_nonneg
    change C.radius ≤ kappa * S.radius at hhi
    nlinarith
  have hCS : C.carrier ⊆ S.carrier := by
    apply hsub.trans
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := S) hkappa1
  have hCrank : C.rank = S.rank := congrArg Finset.card hfreq
  obtain ⟨A, hAS, B, hBT, hA, hB, hAd, hBd, R, hRreg, hRpos, hRwidth, hRC,
      hRrank, hRlower, hRprob⟩ :=
    exists_sifted_almostPeriods L S C hL hCpos hCwidth hCreg (by omega)
      T K hT z hTcard hTB hSL hkappa₀ f hsupport hM (by linarith) (by linarith)
      hepsilon heta heta1 hp hH hcap hf q hqp hmoment hKbad hseparation hKcard
  refine ⟨C, hfreq, hCreg, hCpos, hlo, hhi, hCS, hsub, z, hz, A, hAS, B, hBT, hA, hB, hAd, hBd,
    R, hRreg, hRpos, hRwidth, hRC, hRrank, hRlower, ?_⟩
  have hmean := smoothed_correlation_ge_of_good_probability L.carrier A B K R.carrier f
    (fun x => (hf x).1) (fun _ hx => le_of_mem_goodDifferenceSet hx)
  exact (mul_le_mul_of_nonneg_left hRprob (by linarith : 0 ≤ 1 + c / 4)).trans hmean

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MatchedFlatDecay
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.LocalConvolution

theorem unbalanced_error_control {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < c / 64 ∧ c / 64 ≤ 1 ∧
      1 + c / 8 ≤ (1 + c / 4) * (1 - c / 64 - c / 64) ∧
      1 + c / 16 ≤ (1 + c / 4) * (1 - c / 64 - c / 64) - c / 64 - c / 64 := by
  have hquad : 0 ≤ c * (1 - c) := mul_nonneg hc.le (sub_nonneg.mpr hc1)
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> nlinarith

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UnbalancedBohrShape
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_average_square_mean
    (L A B : Finset (ZMod N)) (hL : L.Nonempty) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : CyclicBohr.Set N) (hRpos : 0 < R.radius) (hRreg : R.IsRankRegular)
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L → f x = 0)
    {M beta epsilon : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hepsilon : 0 < epsilon)
    (hlarge : beta ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L f f (a - b + t)) :
    let sigma := localizedAverageScale R.rank (M ^ 2) epsilon
    ∃ C : CyclicBohr.Set N, C.frequencies = R.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (sigma : ℝ) * R.radius / 4 ≤ C.radius ∧ C.radius ≤ sigma * R.radius / 2 ∧
      C.carrier ⊆ R.carrier ∧
      beta - epsilon ≤ (∑ x, (𝔼 c ∈ C.carrier, f (x + c)) ^ 2) / L.card := by
  intro sigma
  obtain ⟨hsigma0, hsigma, herror⟩ := localizedAverageScale_spec R.rank (sq_nonneg M) hepsilon
  change 0 < sigma at hsigma0
  change sigma ≤ _ at hsigma
  change M ^ 2 * (400 * (max R.rank 1 : ℕ) * (sigma : ℝ)) ≤ epsilon at herror
  have hsigma1 : sigma ≤ 1 := by
    apply hsigma.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max R.rank 1) by omega)
  let kappa : ℝ≥0 := sigma / 2
  have hkappa0 : 0 < kappa := by dsimp [kappa]; positivity
  have hkappa1 : kappa ≤ 1 :=
    (div_le_self hsigma0.le (by norm_num : (1 : ℝ≥0) ≤ 2)).trans hsigma1
  have hkappasum : kappa + kappa = sigma := by dsimp [kappa]; ring
  obtain ⟨C, hfreq, hreg, hlo, hhi, hsub, _⟩ :=
    R.exists_controlled_regular_subdilate hRpos kappa hkappa0 hkappa1
  have hkappaR : (0 : ℝ) < kappa := by exact_mod_cast hkappa0
  have hCpos : 0 < C.radius := (show 0 < (kappa : ℝ) * R.radius / 2 by positivity).trans_le hlo
  have hlo' : (sigma : ℝ) * R.radius / 4 ≤ C.radius := by
    have h : (kappa : ℝ) * R.radius / 2 = (sigma : ℝ) * R.radius / 4 := by
      dsimp [kappa]
      ring
    rwa [h] at hlo
  have hhi' : C.radius ≤ (sigma : ℝ) * R.radius / 2 := by
    have h : (kappa : ℝ) * R.radius = (sigma : ℝ) * R.radius / 2 := by
      dsimp [kappa]
      ring
    rwa [h] at hhi
  have hCR : C.carrier ⊆ R.carrier := by
    apply hsub.trans
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := R) hkappa1
  have hTV : ∀ c ∈ C.carrier, ∀ d ∈ C.carrier,
      (∑ x, |realUniformMass R.carrier (x - (c - d)) - realUniformMass R.carrier x|) ≤
        400 * (max R.rank 1 : ℕ) * (sigma : ℝ) := by
    intro c hc d hd
    have hdiff := CyclicBohr.Set.sub_mem_ndilate (hsub hc) (hsub hd)
    rw [hkappasum] at hdiff
    exact CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hRreg hsigma hdiff
  have henergy := triple_smoothed_correlation_le_square_mean L A B R.carrier C.carrier
    hL hA hB R.carrier_nonempty C.carrier_nonempty f hsupport hf hTV
  refine ⟨C, hfreq, hreg, hCpos, hlo', hhi', hCR, ?_⟩
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_bohr_average_local_second_moment
    (L : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (A B : Finset (ZMod N)) (hA : A.Nonempty) (hB : B.Nonempty)
    (R : CyclicBohr.Set N) (hRpos : 0 < R.radius) (hRreg : R.IsRankRegular)
    {kappa : ℝ≥0} (hRL : R.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M beta epsilon : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hepsilon : 0 < epsilon)
    (hlarge : beta ≤ 𝔼 a ∈ A, 𝔼 b ∈ B, 𝔼 t ∈ R.carrier, correlation L.carrier f f (a - b + t)) :
    let sigma := localizedAverageScale R.rank (M ^ 2) epsilon
    ∃ C : CyclicBohr.Set N, C.frequencies = R.frequencies ∧ C.IsRankRegular ∧ 0 < C.radius ∧
      (sigma : ℝ) * R.radius / 4 ≤ C.radius ∧ C.radius ≤ sigma * R.radius / 2 ∧
      C.carrier ⊆ R.carrier ∧
      beta - epsilon - 200 * (max L.rank 1 : ℕ) * (kappa : ℝ) * M ^ 2 ≤
        𝔼 x ∈ L.carrier, (𝔼 c ∈ C.carrier, f (x + c)) ^ 2 := by
  intro sigma
  obtain ⟨C, hfreq, hreg, hpos, hlo, hhi, hCR, henergy⟩ :=
    exists_bohr_average_square_mean L.carrier A B L.carrier_nonempty hA hB R hRpos hRreg
      f hsupport hf hepsilon hlarge
  have hlocal := square_mean_le_local_add_boundary L hL C.carrier C.carrier_nonempty
    (hCR.trans hRL) hkappa f hsupport hf
  refine ⟨C, hfreq, hreg, hpos, hlo, hhi, hCR, ?_⟩
  linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.Peeling

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

theorem exists_unbalanced_bohr_second_moment_at_scale
    (L S : CyclicBohr.Set N) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    {kappa₀ : ℝ≥0} (hSL : S.carrier ⊆ (L.ndilate kappa₀).carrier)
    (hkappa₀ : kappa₀ ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (f : ZMod N → ℝ) (hsupport : ∀ x, x ∉ L.carrier → f x = 0)
    {M c p H : ℝ} (hM : 0 < M) (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : 1 ≤ p) (hH : 0 ≤ H) (hcap : M ≤ Real.exp p)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hboundary : 200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤ c / 64)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (hqp : (q : ℝ) ≤ H * p)
    (hlarge : 1 + c ≤ differenceLp S.carrier (correlation L.carrier f f) q)
    (hseparation : (1 + c / 4) ^ q ≤ (c / 64) / 2 * (1 + c / 2) ^ q)
    (kappa : ℝ≥0) (hkappa0 : 0 < kappa)
    (hscale : kappa ≤ localizedAverageScale S.rank (M ^ (2 * q))
      ((1 + c) ^ q - (1 + c / 2) ^ q)) :
    let D := (3 * H + 1) * p ^ 2
    ∃ C : CyclicBohr.Set N, C.IsRankRegular ∧ 0 < C.radius ∧ C.radius ≤ 1 ∧
      C.carrier ⊆ S.carrier ∧ C.carrier ⊆ (S.ndilate kappa).carrier ∧
      (C.rank : ℝ) ≤ S.rank + almostPeriodicityWidthConstant (c / 64) * (1 + D) ^ 4 ∧
      ((kappa : ℝ) * (localizedAverageScale C.rank (M ^ 2) (c / 64) : ℝ) * S.radius / 8) *
        Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))) ≤ C.radius ∧
      1 + c / 16 ≤ 𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 := by
  intro D
  have htol : 0 < c / 64 := by positivity
  have hcontrol := unbalanced_error_control hc hc1
  obtain ⟨C₀, hfreq₀, _, _, hlow₀, _, hC₀S, hC₀small, _, _, A, _, B, _, hA, hB, _, _,
      R, hRreg, hRpos, hRwidth, hRC₀, hRrank, hRlow, hlargeR⟩ :=
    exists_smoothing_of_large_correlation_at_scale L S hL hSpos hSwidth hSreg hSrank hSL hkappa₀
      f hsupport hM hc htol htol hcontrol.2.1 hp hH hcap hf q hq heven hqp hlarge hseparation kappa hkappa0 hscale
  have hRSL : R.carrier ⊆ (L.ndilate kappa₀).carrier := (hRC₀.trans hC₀S).trans hSL
  obtain ⟨C, hfreq, hCreg, hCpos, hClow, hChi, hCR, hsecond⟩ :=
    exists_bohr_average_local_second_moment L hL A B hA hB R hRpos hRreg hRSL hkappa₀
      f hsupport hf htol hlargeR
  have hCrank : C.rank = R.rank := congrArg Finset.card hfreq
  have hC₀rank : C₀.rank = S.rank := congrArg Finset.card hfreq₀
  have hsigma1 : (localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) ≤ 1 := by
    exact_mod_cast localizedAverageScale_le_one R.rank (sq_nonneg M) htol
  have hCwidth : C.radius ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hsigma1 R.radius_nonneg
    have hnonneg := (localizedAverageScale R.rank (M ^ 2) (c / 64)).coe_nonneg
    have hRnonneg := R.radius_nonneg
    linarith
  refine ⟨C, hCreg, hCpos, hCwidth, hCR.trans (hRC₀.trans hC₀S),
    hCR.trans (hRC₀.trans hC₀small), ?_, ?_, ?_⟩
  · rw [hCrank]
    simpa only [hC₀rank] using hRrank
  · rw [hCrank]
    have hRlow' : ((kappa : ℝ) * S.radius / 2) *
        Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))) ≤ R.radius := by
      have h := mul_le_mul_of_nonneg_right hlow₀
        (Real.exp_nonneg (-(almostPeriodicityWidthConstant (c / 64) *
          (1 + D + Real.log (2 + S.rank)))))
      exact h.trans (by simpa only [hC₀rank] using hRlow)
    calc
      _ = ((localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) / 4) *
          (((kappa : ℝ) * S.radius / 2) *
            Real.exp (-(almostPeriodicityWidthConstant (c / 64) *
              (1 + D + Real.log (2 + S.rank))))) := by ring
      _ ≤ ((localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) / 4) * R.radius :=
        mul_le_mul_of_nonneg_left hRlow' (by positivity)
      _ = (localizedAverageScale R.rank (M ^ 2) (c / 64) : ℝ) * R.radius / 4 := by ring
      _ ≤ C.radius := hClow
  · change (1 + c / 4) * (1 - c / 64 - c / 64) - c / 64 -
      200 * (max L.rank 1 : ℕ) * (kappa₀ : ℝ) * M ^ 2 ≤
        𝔼 x ∈ L.carrier, cellAverage C.carrier f x ^ 2 at hsecond
    have hgain := hcontrol.2.2.2
    linarith

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

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

theorem solution : type_of% @OAI.Erdos3.LocalConvolution.exists_unbalanced_bohr_second_moment_at_scale := @OAI.Erdos3.LocalConvolution.exists_unbalanced_bohr_second_moment_at_scale
