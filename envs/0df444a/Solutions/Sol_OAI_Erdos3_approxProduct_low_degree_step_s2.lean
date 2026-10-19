-- Prove2me | solution 1 for OAI.Erdos3.approxProduct_low_degree_step_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:16.123568+00:00
-- url     : https://prove2.me/submissions/14dfcc2f-01cc-44b2-90b8-88e4d67038a4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B138
import Definitions.Def_OAIE3v2B139
import Theorems.Thm_OAI_Erdos3_productANOVATensor_uniform_of_normalized_s2
import Theorems.Thm_OAI_Erdos3_productANOVA_moment_bound_of_sections_s2

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

theorem approxMomentBudget_error_le_one (N q : ℕ) {k r : ℕ} (hkr : k ≤ r) {M eta : ℝ}
    (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hbudget : eta * approxMomentEnvelope N r M ^ q ≤ 1 / 2) :
    eta * ((2 : ℝ) ^ k * (N : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1 := by
  have he := approxMomentBudget_eta_le_half N r q hM heta hbudget
  have hterm := (approxMomentEnvelope_bounds_term N k hM (by linarith : eta ≤ 1)).trans
    (approxMomentEnvelope_mono N hkr hM)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hterm q) heta).trans
    (hbudget.trans (by norm_num))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ApproxMomentCutoff
namespace OAI

section

namespace Erdos3

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteEvenMomentTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_le_of_nat_moment (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : (∑ x, w x * |f x| ^ q) ≤ B ^ q) :
    finiteWeightedLp w (q : ℝ) f ≤ B := by
  have hqr : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  apply (Real.rpow_le_rpow_iff (finiteWeightedLp_nonneg w hw _ f) hB hqr).mp
  rw [finiteWeightedLp_rpow_self w hw hqr f]
  simpa only [Real.rpow_natCast] using hm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_le_of_moment_error (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : (∑ x, w x * |f x| ^ q) ≤ B ^ q + 1) :
    finiteWeightedLp w (q : ℝ) f ≤ B + 1 := by
  apply finiteWeightedLp_le_of_nat_moment w hw q hq f (B + 1) (by linarith)
  apply hm.trans
  simpa only [one_pow] using pow_add_pow_le hB (by norm_num : (0 : ℝ) ≤ 1) hq.ne'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finiteWeightedLp_transfer_even (w v : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (q : ℕ) (hq : 0 < q) (heven : Even q) (f : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : |∑ x, v x * f x ^ q| ≤ B ^ q)
    (herr : |(∑ x, w x * f x ^ q) - ∑ x, v x * f x ^ q| ≤ 1) :
    finiteWeightedLp w (q : ℝ) f ≤ B + 1 := by
  apply finiteWeightedLp_le_of_moment_error w hw q hq f B hB
  simp only [heven.pow_abs]
  have hdiff := (abs_le.mp herr).2
  have hmain := (le_abs_self (∑ x, v x * f x ^ q)).trans hm
  linarith

end Erdos3

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteHypergraphAbstract
namespace OAI

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.mono {I : Type*} {X : I → Type*} {S T : Finset I}
    {f : (∀ i, X i) → ℝ} (hf : ProductDependsOn S f) (hST : S ⊆ T) :
    ProductDependsOn T f := fun x y h => hf x y (fun i hi => h i (hST hi))

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem ProductMarginalsClose.mono {rho : (∀ i, X i) → ℝ} {eta : ℝ} {s t : ℕ}
    (h : ProductMarginalsClose μ rho eta s) (ht : t ≤ s) : ProductMarginalsClose μ rho eta t :=
  fun B hB x hx => h B (hB.trans ht) x hx

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

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVAEnergy_nonneg (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    0 ≤ productANOVAEnergy μ D f :=
  Finset.sum_nonneg (fun _ _ => (FiniteProbabilityWeights.pi μ).mean_nonneg (fun _ => sq_nonneg _))

theorem productANOVAEnergy_pairing (D : Finset (Finset I)) (f : (∀ i, X i) → ℝ) :
    productANOVAEnergy μ D f =
      (FiniteProbabilityWeights.pi μ).mean (fun x => f x * productANOVATruncation μ D f x) := by
  simp only [productANOVAEnergy, productANOVATruncation, Finset.mul_sum,
    FiniteProbabilityWeights.mean_sum, productANOVA_pairing_self]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem ProductDependsOn.prod {I J : Type*} {X : I → Type*}
    (S : Finset I) (D : Finset J) (f : J → (∀ i, X i) → ℝ)
    (hf : ∀ j ∈ D, ProductDependsOn S (f j)) :
    ProductDependsOn S (fun x => ∏ j ∈ D, f j x) := by
  intro x y hxy
  exact Finset.prod_congr rfl (fun j hj => hf j hj x y hxy)

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductFamilyMomentComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productFamily_moment_comparison (rho : (∀ i, X i) → ℝ)
    (S : J → Finset I) (u : J → (∀ i, X i) → ℝ) (b q : ℕ) {eta C : ℝ}
    (heta : 0 ≤ eta) (_hC : 0 ≤ C) (hcard : ∀ j, (S j).card ≤ b)
    (hdep : ∀ j, ProductDependsOn (S j) (u j))
    (hcap : ∀ j x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u j x| ≤ C)
    (hclose : ∀ T : Finset I, T.card ≤ q * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ T rho x - 1| ≤ eta) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * (∑ j, u j x) ^ q) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ j, u j x) ^ q)| ≤
        eta * (Fintype.card J : ℝ) ^ q * C ^ q := by
  classical
  have hterm (a : Fin q → J) :
      |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * ∏ j, u (a j) x) -
        (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j, u (a j) x)| ≤ eta * C ^ q := by
    let T := Finset.univ.biUnion (fun j : Fin q => S (a j))
    have hT : T.card ≤ q * b := by
      calc
        T.card ≤ ∑ j : Fin q, (S (a j)).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin q, b := Finset.sum_le_sum (fun j _ => hcard (a j))
        _ = q * b := by simp
    apply productMarginal_test_error μ rho (fun x => ∏ j, u (a j) x) T heta ?_ (hclose T hT) ?_
    · apply ProductDependsOn.prod
      intro j _
      apply (hdep (a j)).mono
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
    · intro x hx
      rw [Finset.abs_prod]
      have h := Finset.prod_le_prod (s := Finset.univ) (fun j _ => abs_nonneg (u (a j) x)) (fun j _ => hcap (a j) x hx)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  simp_rw [Fintype.sum_pow, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin q → J,
        |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * ∏ j, u (a j) x) -
          (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j, u (a j) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin q → J, eta * C ^ q := Finset.sum_le_sum (fun a _ => hterm a)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAWeightedLp
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_comparison (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q)
    (hclose : ProductMarginalsClose μ rho eta (q * k)) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x *
        productANOVATruncation μ (Finset.univ.powersetCard k) (fun y => rho y * F y) x ^ q) -
      (FiniteProbabilityWeights.pi μ).mean (fun x =>
        productANOVATruncation μ (Finset.univ.powersetCard k) (fun y => rho y * F y) x ^ q)| ≤
      eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q := by
  classical
  let D : Finset (Finset I) := Finset.univ.powersetCard k
  let C := (2 : ℝ) ^ k * (M * (1 + eta))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd (j : ↥D) : j.1.card = k := (Finset.mem_powersetCard.mp j.2).2
  have hcap : ∀ (j : ↥D) x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
      |productANOVA μ j.1 (fun y => rho y * F y) x| ≤ C := by
    intro j x hx
    have h := productANOVA_weighted_cap μ rho F hrho hM hF j.1 (by
      intro T hT
      apply hclose T
      have ht := Finset.card_le_card hT
      rw [hd j] at ht
      nlinarith) x hx
    simpa only [hd j] using h
  have h := productFamily_moment_comparison μ rho (fun j : ↥D => j.1)
    (fun j => productANOVA μ j.1 (fun y => rho y * F y)) k q heta hC
    (fun j => (hd j).le) (fun j => productANOVA_depends μ j.1 _) hcap hclose
  simp only [Fintype.card_coe] at h
  have hsum (x : ∀ i, X i) :
      (∑ j : ↥D, productANOVA μ j.1 (fun y => rho y * F y) x) =
        productANOVATruncation μ D (fun y => rho y * F y) x :=
    Finset.sum_coe_sort D (fun S => productANOVA μ S (fun y => rho y * F y) x)
  simp_rw [hsum] at h
  have hcard : (D.card : ℝ) ≤ (Fintype.card I : ℝ) ^ k := by
    dsimp [D]
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast Nat.choose_le_pow (Fintype.card I) k
  calc
    _ ≤ eta * (D.card : ℝ) ^ q * C ^ q := h
    _ ≤ eta * ((Fintype.card I : ℝ) ^ k) ^ q * C ^ q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard q) heta)
        (pow_nonneg hC _)
    _ = _ := by simp only [C, mul_pow]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_weighted_lp_of_sections (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) (C : ℝ) (hC : 0 ≤ C)
    (hclose : ProductMarginalsClose μ rho eta (q * k))
    (herr : eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base (fun x => rho x * F x)) z ≤ C) :
    finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) (q : ℝ)
      (productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
        ((q * k : ℕ) : ℝ) ^ k * C + 1 := by
  let P := productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)
  have hm : |∑ x, (FiniteProbabilityWeights.pi μ).weight x * P x ^ q| ≤
      (((q * k : ℕ) : ℝ) ^ k * C) ^ q := by
    apply (productANOVA_moment_bound_of_sections_s2 μ k q base x₀ _ C hC hsection).trans_eq
    rw [Nat.cast_pow, mul_pow (((q * k : ℕ) : ℝ) ^ k) C q, ← pow_mul, Nat.mul_comm k q]
  have hc := (productANOVA_moment_comparison μ rho F hrho hM heta hF k q hq hclose).trans herr
  apply finiteWeightedLp_transfer_even _ (FiniteProbabilityWeights.pi μ).weight
    (fun x => mul_nonneg ((FiniteProbabilityWeights.pi μ).nonneg x) (hrho x))
    q hq heven P _ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hC) hm
  simpa only [FiniteProbabilityWeights.mean, mul_assoc] using hc

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem approxProduct_low_degree_step_s2_oai (k r q : ℕ) (hk : 0 < k) (hkr : k ≤ r)
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
    (productANOVATensor_uniform_of_normalized_s2 μ k base hK hR _ hLower)
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

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.approxProduct_low_degree_step_s2_oai.{u_1, u_2} := @OAI.Erdos3.approxProduct_low_degree_step_s2_oai.{u_1, u_2}
