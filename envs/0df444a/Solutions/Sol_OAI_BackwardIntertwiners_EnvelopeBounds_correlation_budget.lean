-- Prove2me | solution 1 for OAI.BackwardIntertwiners.EnvelopeBounds.correlation_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:44:48.524253+00:00
-- url     : https://prove2.me/submissions/de06e830-d74a-4f6f-be1b-ccd5262b5b94

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvolutionBounds.lean:L175-L232
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.EnvelopeBounds.correlation_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvexEnvelope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma increment_mono (h : DiscreteConvex F) {i j : ℕ} (hij : i ≤ j) (k : ℕ) :
    F (i+k) - F i ≤ F (j+k) - F j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (Nat.add_le_add_right hij k)
    have e₁ : i + (k+1) = i+k+1 := by omega
    have e₂ : j + (k+1) = j+k+1 := by omega
    rw [e₁, e₂]
    linarith

lemma increment_lower (h : DiscreteConvex F) (q k : ℕ) :
    (k : ℝ) * (F (q+1) - F q) ≤ F (q+k) - F q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (Nat.le_add_right q k)
    have e : q + (k+1) = q+k+1 := by omega
    rw [e]
    push_cast
    nlinarith

lemma increment_upper (h : DiscreteConvex F) (q k r : ℕ) (hkr : q+k ≤ r+1) :
    F (q+k) - F q ≤ (k : ℝ) * (F (r+1) - F r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := h (show q+k ≤ r by omega)
    have ih' := ih (by omega)
    have e : q + (k+1) = q+k+1 := by omega
    rw [e]
    push_cast
    nlinarith

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma tail_term_bound (h : DiscreteConvex F) {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    normalizedTailTerm F q k ≤
      Real.exp (F 1) * Real.exp (-(F (k+2) - F (k+1))) := by
  have hi := h.increment_mono hq (k+1)
  have e₁ : 1+(k+1) = k+2 := by omega
  have e₂ : q+(k+1) = q+k+1 := by omega
  rw [e₁, e₂] at hi
  rw [normalizedTailTerm, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

lemma tail_summable (h : DiscreteConvex F)
    (hsum : Summable (fun n => Real.exp (-(F (n+1) - F n))))
    {q : ℕ} (hq : 1 ≤ q) : Summable (normalizedTailTerm F q) := by
  have hmajor := ((summable_nat_add_iff 1).mpr hsum).mul_left (Real.exp (F 1))
  apply hmajor.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < normalizedTailTerm F q k from Real.exp_pos _)]
  simpa only [Nat.add_assoc] using h.tail_term_bound hq k

end DiscreteConvex

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvolutionBounds ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma middle_exponent {A B : ℕ → ℝ} (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    {m : ℕ} (hm : 1 ≤ m) (p k : ℕ) (hk : k ≤ m) {lam : ℝ}
    (hbridge : A m - A (m-1) + lam ≤ B (p+1) - B p) :
    -B (p+k) - A (m-k) ≤ -B p - A m - lam * k := by
  have hlow := hB.increment_lower p k
  have hupp := hA.increment_upper (m-k) k (m-1) (by omega)
  rw [Nat.sub_add_cancel hk, Nat.sub_add_cancel hm] at hupp
  have hmul := mul_le_mul_of_nonneg_left hbridge (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  nlinarith

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

lemma reflected (hb : EnvelopeBounds A B b c) :
    EnvelopeBounds B A (fun n => c (-n)) (fun n => b (-n)) where
  b_pos := hb.c_neg
  b_neg := by simpa only [neg_neg] using hb.c_pos
  c_pos := hb.b_neg
  c_neg := by simpa only [neg_neg] using hb.b_pos

lemma central_norm (_ : EnvelopeBounds A B b c) {m p : ℕ}
    (hp : ‖b (p : ℤ)‖ = Real.exp (-B p))
    (hm : ‖c (-(m : ℤ))‖ = Real.exp (-A m)) :
    ‖centeredCorrelation b c m p 0‖ = Real.exp (-B p - A m) := by
  simp only [centeredCorrelation, add_zero, norm_mul, hp, hm]
  rw [← Real.exp_add]
  congr 1

lemma middle_pos (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    {m : ℕ} (hm : 1 ≤ m) (p k : ℕ) (hk : k ≤ m) {lam : ℝ}
    (hbridge : A m - A (m-1) + lam ≤ B (p+1) - B p) :
    ‖centeredCorrelation b c m p k‖ ≤
      Real.exp (-B p - A m) * Real.exp (-lam * k) := by
  have he : -(m : ℤ) + k = -((m-k : ℕ) : ℤ) := by omega
  rw [centeredCorrelation, he, ← Nat.cast_add, norm_mul]
  calc ‖b ((p+k : ℕ) : ℤ)‖ * ‖c (-((m-k : ℕ) : ℤ))‖ ≤
      Real.exp (-B (p+k)) * Real.exp (-A (m-k)) :=
      mul_le_mul (hb.b_pos _) (hb.c_neg _) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-B p - A m) * Real.exp (-lam * k) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simpa only [sub_eq_add_neg, neg_mul] using middle_exponent hA hB hm p k hk hbridge

lemma middle_neg (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    {p : ℕ} (hp : 1 ≤ p) (m k : ℕ) (hk : k ≤ p) {lam : ℝ}
    (hbridge : B p - B (p-1) + lam ≤ A (m+1) - A m) :
    ‖centeredCorrelation b c m p (-(k : ℤ))‖ ≤
      Real.exp (-B p - A m) * Real.exp (-lam * k) := by
  have hh := hb.reflected.middle_pos hB hA hp m k hk hbridge
  simpa only [centeredCorrelation, neg_add, neg_neg, mul_comm, neg_add_rev,
    sub_eq_add_neg, add_comm] using hh

lemma tail_pos (hb : EnvelopeBounds A B b c) (m p k : ℕ)
    (hend : B p + A m ≤ B (m+p)) :
    ‖centeredCorrelation b c m p ((m+k+1 : ℕ) : ℤ)‖ ≤
      Real.exp (-B p - A m) * normalizedTailTerm B (m+p) k := by
  have e₁ : (p : ℤ) + ((m+k+1 : ℕ) : ℤ) = ((m+p+k+1 : ℕ) : ℤ) := by omega
  have e₂ : -(m : ℤ) + ((m+k+1 : ℕ) : ℤ) = ((k+1 : ℕ) : ℤ) := by omega
  rw [centeredCorrelation, e₁, e₂, norm_mul]
  calc ‖b ((m+p+k+1 : ℕ) : ℤ)‖ * ‖c ((k+1 : ℕ) : ℤ)‖ ≤
      Real.exp (-B (m+p+k+1)) * Real.exp (B (k+1)) :=
      mul_le_mul (hb.b_pos _) (hb.c_pos _) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [normalizedTailTerm, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)

lemma tail_neg (hb : EnvelopeBounds A B b c) (m p k : ℕ)
    (hend : B p + A m ≤ A (m+p)) :
    ‖centeredCorrelation b c m p (-((p+k+1 : ℕ) : ℤ))‖ ≤
      Real.exp (-B p - A m) * normalizedTailTerm A (m+p) k := by
  have hh := hb.reflected.tail_pos p m k (by simpa [add_comm] using hend)
  simpa only [centeredCorrelation, neg_add, neg_neg, mul_comm, neg_add_rev,
    sub_eq_add_neg, add_comm, Nat.add_comm] using hh

end EnvelopeBounds

lemma tsum_bound_middle_tail {g t u : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (m : ℕ)
    (hg : ∀ k, 0 ≤ g k) (ht : ∀ k, 0 ≤ t k)
    (hst : Summable t) (hsu : Summable u)
    (hmiddle : ∀ k, k < m → g k ≤ M * t k)
    (htail : ∀ k, g (k+m) ≤ M * u k) :
    Summable g ∧ (∑' k, g k) ≤ M * (∑' k, t k) + M * (∑' k, u k) := by
  have htailSum : Summable (fun k => g (k+m)) := by
    apply (hsu.mul_left M).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (hg _)]
    exact htail k
  have hsum : Summable g := (summable_nat_add_iff m).mp htailSum
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add m]
  apply add_le_add
  · calc ∑ k ∈ Finset.range m, g k ≤ ∑ k ∈ Finset.range m, M * t k :=
      Finset.sum_le_sum (fun k hk => hmiddle k (Finset.mem_range.mp hk))
      _ ≤ ∑' k, M * t k := (hst.mul_left M).sum_le_tsum _ (fun k _ => mul_nonneg hM (ht k))
      _ = M * ∑' k, t k := tsum_mul_left
  · calc ∑' k, g (k+m) ≤ ∑' k, M * u k := htailSum.tsum_le_tsum htail (hsu.mul_left M)
      _ = M * ∑' k, u k := tsum_mul_left

lemma central_norm_le_of_correlation_zero (f : ℤ → ℂ)
    (hp : Summable (fun n : ℕ => ‖f (n+1)‖))
    (hn : Summable (fun n : ℕ => ‖f (-(n+1))‖))
    (hz : (∑' n : ℤ, f n) = 0) :
    ‖f 0‖ ≤ (∑' n : ℕ, ‖f (n+1)‖) + ∑' n : ℕ, ‖f (-(n+1))‖ := by
  rw [tsum_of_add_one_of_neg_add_one hp.of_norm hn.of_norm] at hz
  have he : f 0 = -((∑' n : ℕ, f (n+1)) + ∑' n : ℕ, f (-(n+1))) := by
    linear_combination hz
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add (norm_tsum_le_tsum_norm hp) (norm_tsum_le_tsum_norm hn))

lemma geometricMiddle_hasSum {lam : ℝ} (hlam : 0 < lam) :
    HasSum (geometricMiddle lam) (Real.exp (-lam) / (1-Real.exp (-lam))) := by
  have hr : Real.exp (-lam) < 1 := by simpa using hlam
  have hh := (hasSum_geometric_of_lt_one (Real.exp_pos (-lam)).le hr).mul_left (Real.exp (-lam))
  have heq : geometricMiddle lam = (fun k : ℕ => Real.exp (-lam) * Real.exp (-lam)^k) := by
    funext k
    rw [geometricMiddle, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [heq, div_eq_mul_inv]
  exact hh

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

lemma correlation_budget (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hsA : Summable (fun n => Real.exp (-(A (n+1) - A n))))
    (hsB : Summable (fun n => Real.exp (-(B (n+1) - B n))))
    {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) {lam : ℝ} (hlam : 0 < lam)
    (hbridge₁ : A m - A (m-1) + lam ≤ B (p+1) - B p)
    (hbridge₂ : B p - B (p-1) + lam ≤ A (m+1) - A m)
    (hcB : ‖b (p : ℤ)‖ = Real.exp (-B p))
    (hcA : ‖c (-(m : ℤ))‖ = Real.exp (-A m))
    (hz : (∑' n : ℤ, centeredCorrelation b c m p n) = 0) :
    1 ≤ 2 * (∑' k, geometricMiddle lam k) +
      (∑' k, normalizedTailTerm A (m+p) k) +
      (∑' k, normalizedTailTerm B (m+p) k) := by
  let M := Real.exp (-B p - A m)
  have hM : 0 < M := Real.exp_pos _
  have hq : 1 ≤ m+p := by omega
  have hendB : B p + A m ≤ B (m+p) := by
    have hh := middle_exponent hA hB hm p m le_rfl hbridge₁
    simp only [Nat.sub_self, hA0, sub_zero] at hh
    rw [Nat.add_comm p m] at hh
    have hmul := mul_nonneg hlam.le (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hendA : B p + A m ≤ A (m+p) := by
    have hh := middle_exponent hB hA hp m p le_rfl hbridge₂
    simp only [Nat.sub_self, hB0, sub_zero] at hh
    have hmul := mul_nonneg hlam.le (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    linarith
  have hpos := tsum_bound_middle_tail hM.le m
    (g := fun k : ℕ => ‖centeredCorrelation b c m p ((k : ℤ)+1)‖)
    (t := geometricMiddle lam) (u := normalizedTailTerm B (m+p))
    (fun _ => norm_nonneg _) (fun _ => (Real.exp_pos _).le)
    (geometricMiddle_hasSum hlam).summable (hB.tail_summable hsB hq) ?_ ?_
  · have hneg := tsum_bound_middle_tail hM.le p
      (g := fun k : ℕ => ‖centeredCorrelation b c m p (-((k : ℤ)+1))‖)
      (t := geometricMiddle lam) (u := normalizedTailTerm A (m+p))
      (fun _ => norm_nonneg _) (fun _ => (Real.exp_pos _).le)
      (geometricMiddle_hasSum hlam).summable (hA.tail_summable hsA hq) ?_ ?_
    · have hh := central_norm_le_of_correlation_zero _ hpos.1 hneg.1 hz
      rw [hb.central_norm hcB hcA] at hh
      change M ≤ _ at hh
      have hmul : M * 1 ≤ M * (2 * (∑' k, geometricMiddle lam k) +
          (∑' k, normalizedTailTerm A (m+p) k) +
          (∑' k, normalizedTailTerm B (m+p) k)) := by
        nlinarith [hpos.2, hneg.2]
      exact (mul_le_mul_iff_right₀ hM).mp hmul
    · intro k hk
      simpa [geometricMiddle, M] using
        hb.middle_neg hA hB hp m (k+1) (by omega) hbridge₂
    · intro k
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, M]
        using hb.tail_neg m p k hendA
  · intro k hk
    simpa [geometricMiddle, M] using
      hb.middle_pos hA hB hm p (k+1) (by omega) hbridge₁
  · intro k
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, M]
      using hb.tail_pos m p k hendB

end EnvelopeBounds

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners OAI.BackwardIntertwiners.EnvelopeBounds
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.EnvelopeBounds.correlation_budget := @_root_.OAI.BackwardIntertwiners.EnvelopeBounds.correlation_budget
