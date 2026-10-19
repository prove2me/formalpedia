-- Prove2me | solution 1 for OAI.BackwardIntertwiners.no_unbounded_against_min
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:51:32.252698+00:00
-- url     : https://prove2.me/submissions/7e60b35e-9bd3-41a6-92d0-d81afa13995b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean:L137-L204
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.no_unbounded_against_min. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Theorems.Thm_OAI_BackwardIntertwiners_DiscreteConvex_slopes_tendsto
import Theorems.Thm_OAI_BackwardIntertwiners_DiscreteConvex_tail_term_tendsto
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

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

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

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

end EnvelopeBounds

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.CoefficientSupport ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

end CoefficientEnvelope

lemma boundedSideTail_nonneg (B : ℕ → ℝ) (c : ℤ → ℂ) (h : ℤ) (p k : ℕ) :
    0 ≤ boundedSideTail B c h p k := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

lemma boundedSideTail_mono {B : ℕ → ℝ} (hB : DiscreteConvex B)
    (c : ℤ → ℂ) (h : ℤ) {p₀ p : ℕ} (hpp : p₀ ≤ p) (k : ℕ) :
    boundedSideTail B c h p k ≤ boundedSideTail B c h p₀ k := by
  have hh := hB.increment_mono hpp (k+1)
  unfold boundedSideTail
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [← Nat.add_assoc] at hh
  linarith

lemma boundedSideTail_tendsto {B : ℕ → ℝ} (hB : DiscreteConvex B)
    (hs : Tendsto (fun n => B (n+1)-B n) atTop atTop)
    (c : ℤ → ℂ) (h : ℤ) {p₀ : ℕ} (hsum : Summable (boundedSideTail B c h p₀)) :
    Tendsto (fun p => ∑' k, boundedSideTail B c h p k) atTop (𝓝 0) := by
  have hpoint (k : ℕ) : Tendsto (fun p => boundedSideTail B c h p k) atTop (𝓝 0) := by
    have heq : (fun p => boundedSideTail B c h p k) =
        (fun p => normalizedTailTerm B p k * (Real.exp (-B (k+1)) * ‖c (h+(k:ℤ)+1)‖)) := by
      funext p
      unfold boundedSideTail normalizedTailTerm
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq]
    simpa using (hB.tail_term_tendsto hs k).mul_const
      (Real.exp (-B (k+1)) * ‖c (h+(k:ℤ)+1)‖)
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (show ∀ᶠ p : ℕ in atTop, ∀ k,
      ‖boundedSideTail B c h p k‖ ≤ boundedSideTail B c h p₀ k from ?_)
  · simpa using ht
  · filter_upwards [eventually_ge_atTop p₀] with p hp k
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedSideTail_nonneg _ _ _ _ _)]
    exact boundedSideTail_mono hB c h hp k

theorem no_unbounded_against_min {B : ℕ → ℝ} {b c : ℤ → ℂ}
    (hB : DiscreteConvex B) (hB0 : B 0 = 0) {δ : ℝ} (hδ : 0 < δ)
    (hquad : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ B n)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ Real.exp (-B n))
    (hc : ∀ n, 0 < B (n+2) - 2*B (n+1) + B n →
      ‖b ((n+1:ℕ):ℤ)‖ = Real.exp (-B (n+1)))
    {h : ℤ} (hch : c h ≠ 0) (hcmin : ∀ j : ℤ, j < h → c j = 0)
    {p₀ : ℕ} (hsum : Summable (boundedSideTail B c h p₀))
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by
  have hchpos := norm_pos_iff.mpr hch
  have ht := boundedSideTail_tendsto hB (hB.slopes_tendsto hB0 hδ hquad) c h hsum
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht (eventually_lt_nhds hchpos))
  obtain ⟨n, hn, hcurv⟩ := large_curvature hδ hδ hquad (max N (max p₀ (h.toNat+1)))
  let p := n+1
  have hp₀ : p₀ ≤ p := by dsimp [p]; omega
  have hpN : N ≤ p := by dsimp [p]; omega
  have hph : h < (p : ℤ) := by dsimp [p]; omega
  have hcontact : ‖b (p : ℤ)‖ = Real.exp (-B p) := hc n (by simpa using hcurv)
  have htailsum : Summable (boundedSideTail B c h p) := by
    apply hsum.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedSideTail_nonneg _ _ _ _ _)]
    exact boundedSideTail_mono hB c h hp₀ k
  let f := fun i : ℤ => b ((p:ℤ)+i) * c (h+i)
  have hfneg : ∀ k : ℕ, f (-((k:ℤ)+1)) = 0 := by
    intro k
    dsimp [f]
    rw [hcmin _ (by omega), mul_zero]
  have hfbound (k : ℕ) : ‖f ((k:ℤ)+1)‖ ≤ Real.exp (-B p) * boundedSideTail B c h p k := by
    dsimp [f, boundedSideTail]
    rw [norm_mul, ← mul_assoc, ← Real.exp_add]
    have he : -B p + (B p - B (p+k+1)) = -B (p+k+1) := by ring
    rw [he]
    have hi : (p:ℤ)+((k:ℤ)+1) = ((p+k+1:ℕ):ℤ) := by omega
    rw [hi]
    simpa only [add_assoc] using mul_le_mul_of_nonneg_right (hb (p+k+1)) (norm_nonneg (c (h+(k:ℤ)+1)))
  have hfpos : Summable (fun k : ℕ => ‖f ((k:ℤ)+1)‖) := by
    apply (htailsum.mul_left (Real.exp (-B p))).of_norm_bounded
    intro k
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hfbound k
  have hfn : Summable (fun k : ℕ => ‖f (-((k:ℤ)+1))‖) := by
    simp only [hfneg, norm_zero]
    exact summable_zero
  have hzcenter : (∑' i : ℤ, f i) = 0 := by
    let r := ((p:ℤ)-h).toNat
    have hr : 1 ≤ r := by dsimp [r]; omega
    have hri : (r:ℤ) = (p:ℤ)-h := by dsimp [r]; omega
    calc (∑' i : ℤ, f i) = ∑' i : ℤ, b ((p:ℤ)+i) * c (((p:ℤ)+i)-(r:ℤ)) := by
          apply tsum_congr
          intro i
          dsimp [f]
          congr 2
          omega
      _ = ∑' j : ℤ, b j * c (j-r) := by
          simpa only [Equiv.coe_addLeft] using
            (Equiv.addLeft (p:ℤ)).tsum_eq (fun j : ℤ => b j * c (j-r))
      _ = 0 := hz r hr
  have hcentral := central_norm_le_of_correlation_zero f hfpos hfn hzcenter
  simp only [hfneg, norm_zero, tsum_zero, add_zero] at hcentral
  have hcentral' : Real.exp (-B p) * ‖c h‖ ≤
      Real.exp (-B p) * ∑' k, boundedSideTail B c h p k := by
    calc Real.exp (-B p) * ‖c h‖ = ‖f 0‖ := by simp [f, hcontact]
      _ ≤ ∑' k : ℕ, ‖f ((k:ℤ)+1)‖ := hcentral
      _ ≤ ∑' k, Real.exp (-B p) * boundedSideTail B c h p k :=
        hfpos.tsum_le_tsum hfbound (htailsum.mul_left _)
      _ = _ := tsum_mul_left
  have hle := (mul_le_mul_iff_right₀ (Real.exp_pos (-B p))).mp hcentral'
  exact (not_lt_of_ge hle) (hN p hpN)

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.no_unbounded_against_min := @_root_.OAI.BackwardIntertwiners.no_unbounded_against_min
