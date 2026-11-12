-- Prove2me | solution 1 for HolonomicPositivity.Robust.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:51:34.170935+00:00
-- url     : https://prove2.me/submissions/d348f514-3c19-4bf1-bee3-e3566f4343c7

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Recurrence
import Definitions.Def_HolonomicPositivity_Robust_Conditions
import Theorems.Thm_HolonomicPositivity_Robust_lemma_5_4

section
set_option autoImplicit false
namespace HolonomicPositivity.Dev.L51
open HolonomicPositivity.Robust

theorem eventually_eval_ne (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (n : ℝ) ≠ 0 := by
  obtain ⟨b, hb⟩ := (p.roots.toFinset.finite_toSet.bddAbove)
  refine ⟨⌈b⌉₊ + 1, fun n hn h0 => ?_⟩
  have hmem : (n : ℝ) ∈ p.roots.toFinset := by
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hp, h0]
  have h1 : (n : ℝ) ≤ b := hb hmem
  have h2 : b ≤ ⌈b⌉₊ := Nat.le_ceil b
  have h3 : ((⌈b⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h3
  linarith

theorem identity (a b c P Q s0 s1 s2 l0 l1 : ℝ) :
    let B := 1 - s2
    let A := B * s1 + P
    let C := A * s0 + Q
    let d := c + P * b + Q * a
    (d - s2 * c) - l1 * (c - s1 * b) =
      (B - l1) * ((c - s1 * b) - l0 * (b - s0 * a)) +
      (l0 * (B - l1) + A) * (b - s0 * a) + C * a := by
  intro B A C d
  simp only [B, A, C, d]
  ring

end HolonomicPositivity.Dev.L51
namespace HolonomicPositivity.Robust
open HolonomicPositivity.Dev.L51 in
theorem chk_lemma_5_1 (P Q : RatFunc ℝ) (hP : NoPolesOnNat P) (hQ : NoPolesOnNat Q)
    (hQ0 : ∀ n : ℕ, ev Q n ≠ 0) (hII : ConditionII P Q) :
    ∃ (S L : RatFunc ℝ) (N : ℕ),
      (∀ n : ℕ, N ≤ n → S.denom.eval (n : ℝ) ≠ 0 ∧ L.denom.eval (n : ℝ) ≠ 0) ∧
      ∀ f : ℕ → ℝ, IsSolution P Q f →
        ∀ n : ℕ, N ≤ n → Certificate S L f n → Certificate S L f (n + 1) := by
  obtain ⟨S, hS0, ⟨_, _, L, hL1, hL2, hL3⟩, hC⟩ := HolonomicPositivity.Robust.lemma_5_4 P Q hP hQ hQ0 hII
  obtain ⟨M0, h0⟩ := Filter.eventually_atTop.1 hS0
  obtain ⟨M1, h1⟩ := Filter.eventually_atTop.1 hL1
  obtain ⟨M2, h2⟩ := Filter.eventually_atTop.1 hL2
  obtain ⟨M3, h3⟩ := Filter.eventually_atTop.1 hL3
  obtain ⟨M4, h4⟩ := Filter.eventually_atTop.1 hC
  obtain ⟨NS, hNS⟩ := eventually_eval_ne S.denom (RatFunc.denom_ne_zero S)
  obtain ⟨NL, hNL⟩ := eventually_eval_ne L.denom (RatFunc.denom_ne_zero L)
  set M : ℝ := max (max (max M0 M1) (max M2 M3)) M4 with hM
  have hM0 : M0 ≤ M := by simp [hM]
  have hM1 : M1 ≤ M := by simp [hM]
  have hM2 : M2 ≤ M := by simp [hM]
  have hM3 : M3 ≤ M := by simp [hM]
  have hM4 : M4 ≤ M := by simp [hM]
  refine ⟨S, L, NS + NL + ⌈M⌉₊ + 1, fun n hn => ⟨hNS n (by omega), hNL n (by omega)⟩, ?_⟩
  intro f hf n hn hcert
  have hnM : M + 1 ≤ (n : ℝ) := by
    have h1 : M ≤ ⌈M⌉₊ := Nat.le_ceil M
    have h2 : ((⌈M⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈M⌉₊ + 1 ≤ n)
    push_cast at h2
    linarith
  have hS : 0 ≤ ev S n := h0 n (by linarith)
  have hLpos : 0 < ev L n := by
    have := h1 ((n : ℝ) - 1) (by linarith)
    simpa using this
  have hBL : ev L ((n : ℝ) + 1) < scaledB S n := h2 n (by linarith)
  have hW : 0 ≤ ev L n * (scaledB S n - ev L ((n : ℝ) + 1)) + scaledA P S n := h3 n (by linarith)
  have hCn : 0 ≤ scaledC P Q S n := h4 n (by linarith)
  unfold Certificate at hcert ⊢
  simp only [scaledDiff] at hcert ⊢
  obtain ⟨hf0, hg0, hh0⟩ := hcert
  have hrec := hf n
  have hid := identity (f n) (f (n+1)) (f (n+2)) (ev P n) (ev Q n) (ev S n)
    (ev S ((n:ℝ)+1)) (ev S ((n:ℝ)+2)) (ev L n) (ev L ((n:ℝ)+1))
  simp only at hid
  have e1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have e2 : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  have hAdef : scaledA P S n = scaledB S n * ev S ((n:ℝ)+1) + ev P n := rfl
  have hBdef : scaledB S n = 1 - ev S ((n:ℝ)+2) := rfl
  have hCdef : scaledC P Q S n = scaledA P S n * ev S n + ev Q n := rfl
  rw [e1] at hh0 ⊢
  have hd : f (n + 3) = f (n+2) + ev P n * f (n+1) + ev Q n * f n := hrec
  rw [← hBdef, ← hAdef, ← hCdef] at hid
  have hh1 : 0 < f (n + 1 + 1 + 1) - ev S ((n:ℝ) + 2) * f (n + 1 + 1) -
      ev L ((n:ℝ) + 1) * (f (n + 1 + 1) - ev S ((n:ℝ) + 1) * f (n + 1)) := by
    have : f (n + 1 + 1 + 1) = f (n + 3) := rfl
    rw [this, hd]
    have hA : 0 ≤ ev L n * (scaledB S n - ev L ((n : ℝ) + 1)) + scaledA P S n := hW
    have t1 : 0 < (scaledB S n - ev L ((n : ℝ) + 1)) * (f (n + 1 + 1) - ev S ((n:ℝ) + 1) * f (n + 1) - ev L ((n:ℝ)) * (f (n + 1) - ev S (n:ℝ) * f n)) :=
      mul_pos (by linarith) hh0
    have t2 := mul_nonneg hA hg0.le
    have t3 := mul_nonneg hCn hf0.le
    linarith [hid]
  have hg1 : 0 < f (n + 1 + 1) - ev S ((n:ℝ) + 1) * f (n + 1) := by
    have : 0 < ev L n * (f (n + 1) - ev S (n:ℝ) * f n) := mul_pos hLpos hg0
    linarith
  have hf1 : 0 < f (n + 1) := by
    have := mul_nonneg hS hf0.le
    linarith
  have e3 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [e3]
  exact ⟨hf1, hg1, hh1⟩
end HolonomicPositivity.Robust
end

theorem solution : type_of% @HolonomicPositivity.Robust.chk_lemma_5_1 := @HolonomicPositivity.Robust.chk_lemma_5_1
