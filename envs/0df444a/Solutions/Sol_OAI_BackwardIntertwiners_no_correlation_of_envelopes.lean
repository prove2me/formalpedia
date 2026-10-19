-- Prove2me | solution 1 for OAI.BackwardIntertwiners.no_correlation_of_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:46:31.075981+00:00
-- url     : https://prove2.me/submissions/0c50b71a-a303-4f5d-87e0-19c82eda7b73

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvolutionBounds.lean:L238-L314
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.no_correlation_of_envelopes. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Theorems.Thm_OAI_BackwardIntertwiners_DiscreteConvex_slopes_tendsto
import Theorems.Thm_OAI_BackwardIntertwiners_DiscreteConvex_tail_term_tendsto
import Theorems.Thm_OAI_BackwardIntertwiners_EnvelopeBounds_correlation_budget
import Theorems.Thm_OAI_BackwardIntertwiners_large_curvature

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvexEnvelope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma step (h : DiscreteConvex F) (n : ℕ) :
    F (n+1) - F n ≤ F (n+2) - F (n+1) := by
  exact h (Nat.le_succ n)

lemma sub_zero_le (h : DiscreteConvex F) (n : ℕ) :
    F n - F 0 ≤ (n : ℝ) * (F (n+1) - F n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hs := h.step n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith

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

lemma summable_exp_neg_slope (h : DiscreteConvex F) (h0 : F 0 = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ F n) :
    Summable (fun n => Real.exp (-(F (n+1) - F n))) := by
  have hgeo : Summable (fun n : ℕ => Real.exp (-δ) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using hδ)
  apply hgeo.of_norm_bounded_eventually_nat
  filter_upwards [hq, eventually_ge_atTop 1] with n hqn hn1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs := h.sub_zero_le n
  rw [h0, sub_zero] at hs
  have hd : δ * n ≤ F (n+1) - F n := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by nlinarith)

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

lemma tail_tsum_tendsto (h : DiscreteConvex F)
    (hsum : Summable (fun n => Real.exp (-(F (n+1) - F n))))
    (hs : Tendsto (fun n => F (n+1) - F n) atTop atTop) :
    Tendsto (fun q => ∑' k, normalizedTailTerm F q k) atTop (𝓝 0) := by
  have hmajor := ((summable_nat_add_iff 1).mpr hsum).mul_left (Real.exp (F 1))
  have hh := tendsto_tsum_of_dominated_convergence hmajor
    (fun k => h.tail_term_tendsto hs k) (show ∀ᶠ q : ℕ in atTop, ∀ k,
      ‖normalizedTailTerm F q k‖ ≤
        Real.exp (F 1) * Real.exp (-(F (k+1+1) - F (k+1))) from ?_)
  · simpa using hh
  · filter_upwards [eventually_ge_atTop 1] with q hq k
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

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

end EnvelopeBounds

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

lemma geometricMiddle_budget {lam : ℝ} (hlam : Real.log 3 < lam) :
    2 * (∑' k, geometricMiddle lam k) < 1 := by
  have hl0 : 0 < lam := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans hlam
  rw [(geometricMiddle_hasSum hl0).tsum_eq]
  have he : (3 : ℝ) < Real.exp lam := by
    have h := Real.exp_lt_exp.mpr hlam
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)] at h
    exact h
  have hrpos : 0 < Real.exp (-lam) := Real.exp_pos _
  have hrlt : Real.exp (-lam) < 1 := by simpa using hl0
  have hprod : Real.exp lam * Real.exp (-lam) = 1 := by
    rw [← Real.exp_add]; simp
  have hsmall := mul_lt_mul_of_pos_right he hrpos
  rw [hprod] at hsmall
  have hden : 0 < 1 - Real.exp (-lam) := sub_pos.mpr hrlt
  calc 2 * (Real.exp (-lam) / (1-Real.exp (-lam))) =
      (2 * Real.exp (-lam)) / (1-Real.exp (-lam)) := by ring
    _ < 1 := (div_lt_one hden).mpr (by linarith)

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

end EnvelopeBounds

theorem no_correlation_of_envelopes {A B : ℕ → ℝ} {b c : ℤ → ℂ}
    (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    {lam δ : ℝ} (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqa : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ A n)
    (hqb : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ B n)
    (hcA : ∀ n, 0 < A (n+2) - 2*A (n+1) + A n →
      ‖c (-((n+1 : ℕ) : ℤ))‖ = Real.exp (-A (n+1)))
    (hcB : ∀ n, 0 < B (n+2) - 2*B (n+1) + B n →
      ‖b ((n+1 : ℕ) : ℤ)‖ = Real.exp (-B (n+1)))
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by
  have hl0 : 0 < lam := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans hlam
  have hδ0 : 0 < δ := hl0.trans hδ
  have hsA := hA.summable_exp_neg_slope hA0 hδ0 hqa
  have hsB := hB.summable_exp_neg_slope hB0 hδ0 hqb
  have htA := hA.slopes_tendsto hA0 hδ0 hqa
  have htB := hB.slopes_tendsto hB0 hδ0 hqb
  have ht : Tendsto (fun q => 2 * (∑' k, geometricMiddle lam k) +
      (∑' k, normalizedTailTerm A q k) + (∑' k, normalizedTailTerm B q k))
      atTop (𝓝 (2 * ∑' k, geometricMiddle lam k)) := by
    simpa using (tendsto_const_nhds.add (hA.tail_tsum_tendsto hsA htA)).add
      (hB.tail_tsum_tendsto hsB htB)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht (eventually_lt_nhds (geometricMiddle_budget hlam)))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (htA (eventually_ge_atTop (B 1 - B 0 - lam)))
  obtain ⟨n, hn, hcurv⟩ := large_curvature hδ0 hδ hqa (max N K)
  let m := n+1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hthreshold : B 1 - B 0 ≤ A m - A (m-1) + lam := by
    have hh := hK n (le_trans (le_max_right _ _) hn)
    change B 1 - B 0 - lam ≤ A (n+1) - A n at hh
    dsimp [m]
    simpa only [Nat.add_sub_cancel] using (show B 1 - B 0 ≤ A (n+1) - A n + lam by linarith)
  let C := A m - A (m-1) + lam
  have hex : ∃ p : ℕ, C < B (p+1) - B p := by
    have he : ∀ᶠ p : ℕ in atTop, C < B (p+1) - B p := htB (eventually_gt_atTop C)
    exact he.exists
  let p := Nat.find hex
  have hright : C < B (p+1) - B p := Nat.find_spec hex
  have hp : 1 ≤ p := by
    by_contra! hh
    have hp0 : p = 0 := by omega
    rw [hp0] at hright
    simp only [zero_add] at hright
    exact (not_lt_of_ge hthreshold) hright
  have hleft : B p - B (p-1) ≤ C := by
    have hh := Nat.find_min hex (show p-1 < p by omega)
    simpa only [Nat.sub_add_cancel hp, not_lt] using hh
  have hcontact : 0 < B ((p-1)+2) - 2*B ((p-1)+1) + B (p-1) := by
    have e₁ : p-1+1 = p := by omega
    have e₂ : p-1+2 = p+1 := by omega
    rw [e₁, e₂]
    linarith
  have hcB' : ‖b (p : ℤ)‖ = Real.exp (-B p) := by
    simpa only [Nat.sub_add_cancel hp] using hcB (p-1) hcontact
  have hcA' : ‖c (-(m : ℤ))‖ = Real.exp (-A m) := hcA n (by linarith)
  have hbridge₂ : B p - B (p-1) + lam ≤ A (m+1) - A m := by
    dsimp [C, m] at hleft ⊢
    have e : n+1+1 = n+2 := by omega
    rw [e]
    linarith
  have hzcenter : (∑' i : ℤ, centeredCorrelation b c m p i) = 0 := by
    calc (∑' i : ℤ, centeredCorrelation b c m p i) =
        ∑' i : ℤ, b ((p : ℤ)+i) * c (((p : ℤ)+i) - ((m+p : ℕ) : ℤ)) := by
          apply tsum_congr
          intro i
          unfold centeredCorrelation
          congr 2
          omega
      _ = ∑' j : ℤ, b j * c (j-((m+p : ℕ) : ℤ)) := by
        simpa only [Equiv.coe_addLeft, add_comm] using
          (Equiv.addLeft (p : ℤ)).tsum_eq (fun j : ℤ => b j * c (j-((m+p : ℕ) : ℤ)))
      _ = 0 := hz (m+p) (by omega)
  have hbudget := hb.correlation_budget hA hB hA0 hB0 hsA hsB hm hp hl0 hright.le
    hbridge₂ hcB' hcA' hzcenter
  have hqN : N ≤ m+p := by dsimp [m]; have := le_trans (le_max_left N K) hn; omega
  exact (not_lt_of_ge hbudget) (hN (m+p) hqN)

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.no_correlation_of_envelopes := @_root_.OAI.BackwardIntertwiners.no_correlation_of_envelopes
