-- Prove2me | solution 1 for OAI.BackwardIntertwiners.CoefficientEnvelope.properties
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:48:19.341401+00:00
-- url     : https://prove2.me/submissions/cad55ceb-748f-4f08-9e08-da4920e89d1e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/CoefficientSupport.lean:L38-L64
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.CoefficientEnvelope.properties. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Theorems.Thm_OAI_BackwardIntertwiners_ConvexEnvelope_contact
import Theorems.Thm_OAI_BackwardIntertwiners_ConvexEnvelope_convex

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

lemma secant_le (h : DiscreteConvex F) {n m : ℕ} (hnm : n ≤ m) :
    (m : ℝ) * (F n - F 0) ≤ (n : ℝ) * (F m - F 0) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hs := h.sub_zero_le n
    have hd := h hnm
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ht : F n - F 0 ≤ (n : ℝ) * (F (m+1) - F m) := by
      calc F n - F 0 ≤ (n : ℝ) * (F (n+1) - F n) := hs
           _ ≤ (n : ℝ) * (F (m+1) - F m) := mul_le_mul_of_nonneg_left hd hn0
    push_cast
    nlinarith

lemma le_endpoint (h : DiscreteConvex F) (h0 : F 0 = 0)
    {n m : ℕ} (hnm : n ≤ m) (hm : 0 < m) (B : ℝ) (hB : 0 ≤ B)
    (hend : F m ≤ B) : F n ≤ B := by
  have hs := h.secant_le hnm
  rw [h0, sub_zero, sub_zero] at hs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  have hh : (m : ℝ) * F n ≤ (m : ℝ) * B := calc
    (m : ℝ) * F n ≤ (n : ℝ) * F m := hs
    _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_left hend hn0
    _ ≤ (m : ℝ) * B := mul_le_mul_of_nonneg_right hnm' hB
  exact (mul_le_mul_iff_right₀ hm0).mp hh

end DiscreteConvex

namespace ConvexEnvelope

variable {I : Set ℕ} {f : ℕ → ℝ}
variable (hunbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ I)
variable (hne : (convexMinorants I f).Nonempty)

include hunbounded in
lemma bddAbove (n : ℕ) :
    BddAbove ((fun F : ℕ → ℝ => F n) '' convexMinorants I f) := by
  obtain ⟨k, hnk, hkI⟩ := hunbounded n
  refine ⟨max 0 (f k), ?_⟩
  rintro _ ⟨F, hF, rfl⟩
  exact hF.2.1.le_endpoint hF.1 (Nat.le_of_lt hnk) (by omega)
    _ (le_max_left _ _) ((hF.2.2 k hkI).trans (le_max_right _ _))

include hunbounded in
lemma le_envelope {F : ℕ → ℝ} (hF : F ∈ convexMinorants I f) (n : ℕ) :
    F n ≤ convexEnvelope I f n := by
  exact le_csSup (bddAbove hunbounded n) ⟨F, hF, rfl⟩

include hunbounded hne in
lemma zero : convexEnvelope I f 0 = 0 := by
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨F, hF, rfl⟩
    exact le_of_eq hF.1
  · obtain ⟨F, hF⟩ := hne
    simpa only [hF.1] using le_envelope hunbounded hF 0

include hne in
lemma below {n : ℕ} (hn : n ∈ I) : convexEnvelope I f n ≤ f n := by
  apply csSup_le (hne.image _)
  rintro _ ⟨F, hF, rfl⟩
  exact hF.2.2 n hn

end ConvexEnvelope

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

namespace DiscreteConvex

variable {F : ℕ → ℝ}

end DiscreteConvex

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

include hu in
lemma unbounded : ∀ n : ℕ, ∃ k, n < k ∧ k ∈ coefficientObstacle d := by
  intro n
  obtain ⟨k, hk, hd⟩ := hu n
  exact ⟨k, hk, by exact ⟨by omega, hd⟩⟩

include hG hG0 hb in
lemma minorant : G ∈ convexMinorants (coefficientObstacle d) (fun n => -Real.log ‖d n‖) := by
  refine ⟨hG0, hG, ?_⟩
  intro n hn
  have hn0 : 0 < ‖d n‖ := norm_pos_iff.mpr hn.2
  have hh := Real.log_le_log hn0 (hb n)
  rw [Real.log_exp] at hh
  linarith

include hu hG hG0 hb in
lemma properties :
    coefficientEnvelope d 0 = 0 ∧ DiscreteConvex (coefficientEnvelope d) ∧
    (∀ n, G n ≤ coefficientEnvelope d n) ∧
    (∀ n, ‖d n‖ ≤ Real.exp (-coefficientEnvelope d n)) ∧
    (∀ n, 0 < coefficientEnvelope d (n+2) - 2*coefficientEnvelope d (n+1) +
      coefficientEnvelope d n → ‖d (n+1)‖ = Real.exp (-coefficientEnvelope d (n+1))) := by
  have hm := minorant hG hG0 hb
  have he : (convexMinorants (coefficientObstacle d) (fun n => -Real.log ‖d n‖)).Nonempty := ⟨G, hm⟩
  have hU := unbounded hu
  refine ⟨ConvexEnvelope.zero hU he, ConvexEnvelope.convex hU he,
    ConvexEnvelope.le_envelope hU hm, ?_, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa only [coefficientEnvelope, ConvexEnvelope.zero hU he, hG0] using hb 0
    · by_cases hd : d n = 0
      · simp only [hd, norm_zero]; exact (Real.exp_pos _).le
      · have hbelow := ConvexEnvelope.below he (show n ∈ coefficientObstacle d from ⟨by omega, hd⟩)
        have hlog : Real.log ‖d n‖ ≤ -coefficientEnvelope d n := by
          change coefficientEnvelope d n ≤ -Real.log ‖d n‖ at hbelow
          linarith
        simpa only [Real.exp_log (norm_pos_iff.mpr hd)] using Real.exp_le_exp.mpr hlog
  · intro n hn
    obtain ⟨hd, hc⟩ := ConvexEnvelope.contact hU he n hn
    change coefficientEnvelope d (n+1) = -Real.log ‖d (n+1)‖ at hc
    rw [hc, neg_neg, Real.exp_log (norm_pos_iff.mpr hd.2)]

end CoefficientEnvelope

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners OAI.BackwardIntertwiners.CoefficientEnvelope
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.CoefficientEnvelope.properties := @_root_.OAI.BackwardIntertwiners.CoefficientEnvelope.properties
