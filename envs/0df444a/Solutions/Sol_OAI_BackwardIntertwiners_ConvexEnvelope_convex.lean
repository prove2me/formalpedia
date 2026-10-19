-- Prove2me | solution 1 for OAI.BackwardIntertwiners.ConvexEnvelope.convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:36:15.367036+00:00
-- url     : https://prove2.me/submissions/da04a6f9-0b43-409b-a915-5bf306cb49cd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean:L130-L142
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.ConvexEnvelope.convex. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvexEnvelope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace DiscreteConvex

variable {F : ℕ → ℝ}

lemma of_step (h : ∀ n, F (n+1) - F n ≤ F (n+2) - F (n+1)) :
    DiscreteConvex F := by
  exact monotone_nat_of_le_succ h

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
lemma convex : DiscreteConvex (convexEnvelope I f) := by
  apply DiscreteConvex.of_step
  intro n
  have hh : convexEnvelope I f (n+1) ≤
      (convexEnvelope I f n + convexEnvelope I f (n+2)) / 2 := by
    apply csSup_le (hne.image _)
    rintro _ ⟨F, hF, rfl⟩
    have hc := hF.2.1.step n
    have hl := le_envelope hunbounded hF n
    have hr := le_envelope hunbounded hF (n+2)
    linarith
  linarith

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

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners OAI.BackwardIntertwiners.ConvexEnvelope
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.ConvexEnvelope.convex := @_root_.OAI.BackwardIntertwiners.ConvexEnvelope.convex
