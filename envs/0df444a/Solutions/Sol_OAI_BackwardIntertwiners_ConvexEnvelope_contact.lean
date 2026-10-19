-- Prove2me | solution 1 for OAI.BackwardIntertwiners.ConvexEnvelope.contact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:37:42.484147+00:00
-- url     : https://prove2.me/submissions/19b004b6-9dfa-46c2-98e7-b1a8ef617f8e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ConvexEnvelope.lean:L154-L191
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.ConvexEnvelope.contact. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Theorems.Thm_OAI_BackwardIntertwiners_ConvexEnvelope_convex

-- ---- from OAI.Analysis.BackwardIntertwiners.ConvexEnvelope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

lemma bump (h : DiscreteConvex F) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hgap : 2 * ε ≤ F (n+2) - 2 * F (n+1) + F n) :
    DiscreteConvex (fun k => F k + if k = n+1 then ε else 0) := by
  apply of_step
  intro k
  by_cases hk : k = n
  · subst k
    have hne : n ≠ n+1 := by omega
    have hne' : n+2 ≠ n+1 := by omega
    simp only [ite_eq_right hne, ite_eq_right hne', ite_true, add_zero]
    linarith
  · have hmid : k+1 ≠ n+1 := by omega
    have hlo : F k ≤ F k + if k = n+1 then ε else 0 := by
      split_ifs <;> linarith
    have hhi : F (k+2) ≤ F (k+2) + if k+2 = n+1 then ε else 0 := by
      split_ifs <;> linarith
    simp only [ite_eq_right hmid, add_zero]
    have hs := h.step k
    linarith

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

include hunbounded hne in
lemma mem : convexEnvelope I f ∈ convexMinorants I f :=
  ⟨zero hunbounded hne, convex hunbounded hne, fun _ hn => below hne hn⟩

include hunbounded hne in

lemma contact (n : ℕ)
    (hgap : 0 < convexEnvelope I f (n+2) - 2 * convexEnvelope I f (n+1) +
      convexEnvelope I f n) :
    n+1 ∈ I ∧ convexEnvelope I f (n+1) = f (n+1) := by
  let F := convexEnvelope I f
  let δ := F (n+2) - 2 * F (n+1) + F n
  have hδ : 0 < δ := hgap
  have hF : F ∈ convexMinorants I f := mem hunbounded hne
  have maximal : ∀ ε : ℝ, 0 < ε → 2*ε ≤ δ →
      (n+1 ∈ I → F (n+1)+ε ≤ f (n+1)) → False := by
    intro ε hε hεgap hεobs
    let G := fun k => F k + if k = n+1 then ε else 0
    have hG : G ∈ convexMinorants I f := by
      refine ⟨?_, hF.2.1.bump n hε.le hεgap, ?_⟩
      · simp [G, hF.1]
      · intro k hk
        by_cases he : k = n+1
        · subst k
          simpa [G] using hεobs hk
        · simpa [G, he] using hF.2.2 k hk
    have hle := le_envelope hunbounded hG (n+1)
    simp only [G, ite_true] at hle
    change F (n+1) + ε ≤ F (n+1) at hle
    linarith
  have hi : n+1 ∈ I := by
    by_contra hn
    exact maximal (δ/4) (by positivity) (by linarith) (by simp [hn])
  refine ⟨hi, ?_⟩
  have hle := hF.2.2 (n+1) hi
  by_contra hneq
  have hlt : F (n+1) < f (n+1) := lt_of_le_of_ne hle hneq
  let ε := min (δ/4) ((f (n+1) - F (n+1))/2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hε₁ : ε ≤ δ/4 := min_le_left _ _
  have hε₂ : ε ≤ (f (n+1) - F (n+1))/2 := min_le_right _ _
  exact maximal ε hε (by linarith) (by intro _; linarith)

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


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.ConvexEnvelope.contact := @_root_.OAI.BackwardIntertwiners.ConvexEnvelope.contact
