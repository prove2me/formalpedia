-- Prove2me | solution 1 for GlobalTheory.GenEigen.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:08.342524+00:00
-- url     : https://prove2.me/submissions/30d65565-050a-47ee-a6e0-bc6b5191eeab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramified
import Theorems.Thm_GlobalTheory_GenEigen_mem_of_add_nil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GenEigen
namespace GlobalTheory.GenEigen
theorem _root_.solution {O B : Type*} [CommRing O] [CommRing B] (a p : O →+* B) (J : Ideal B)
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d) (ε : O)
    (h1 : ∃ y, ε * ε - ε = (l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (l ^ d) - x) = (l : O) * y)
    (hS : ∀ y, (l : B) * (a y - p y) ∈ J)
    (hreg : ∀ (e : O) b, p (1 + l * e) * b ∈ J → b ∈ J)
    (hnil : ∀ x, ∃ k : ℕ, (a x - p x) ^ k ∈ J)
    (hlim : ∃ n : ℕ, 1 - a (ε ^ (l ^ n)) ∈ J) (x : O) : a x - p x ∈ J := by
  have hε : a ε - p ε ∈ J := by
    obtain ⟨y, hy⟩ := h1
    obtain ⟨k, hk⟩ := hnil ε
    have ha : a ε * a ε - a ε = l * a y := by simpa using congrArg a hy
    have hp : p ε * p ε - p ε = l * p y := by simpa using congrArg p hy
    refine mem_of_add_nil J (2 * p ε - 1) (a ε - p ε) _ ?_ k hk ?_
    · intro b hb
      apply hreg (4 * y)
      have : p (1 + l * (4 * y)) * b = (2 * p ε - 1) * ((2 * p ε - 1) * b) := by
        simp only [map_add, map_mul, map_one, map_natCast, map_ofNat]
        linear_combination (-4 * b) * hp
      rw [this]
      exact J.mul_mem_left _ hb
    · have : (2 * p ε - 1 + (a ε - p ε)) * (a ε - p ε) = l * (a y - p y) := by
        linear_combination ha - hp
      rw [this]
      exact hS y
  have ht : (a x ^ (l ^ d) - a x) - (p x ^ (l ^ d) - p x) ∈ J := by
    obtain ⟨y, hy⟩ := h2 x
    obtain ⟨n, hn⟩ := hlim
    have ha : a ε * (a x ^ (l ^ d) - a x) = l * a y := by simpa using congrArg a hy
    have hp : p ε * (p x ^ (l ^ d) - p x) = l * p y := by simpa using congrArg p hy
    set s := a x ^ (l ^ d) - a x
    set t := p x ^ (l ^ d) - p x
    have h3 : a ε * (s - t) ∈ J := by
      have : a ε * (s - t) = l * (a y - p y) - t * (a ε - p ε) := by
        linear_combination ha - hp
      rw [this]
      exact J.sub_mem (hS y) (J.mul_mem_left _ hε)
    obtain ⟨j, hj⟩ : ∃ j, l ^ n = j + 1 := ⟨l ^ n - 1, by have := pow_pos hl n; omega⟩
    rw [hj, map_pow] at hn
    have : s - t = (s - t) * (1 - a ε ^ (j + 1)) + a ε ^ j * (a ε * (s - t)) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hn) (J.mul_mem_left _ h3)
  obtain ⟨H, hH⟩ := Polynomial.powAddExpansion (p x) (a x - p x) (l ^ d)
  obtain ⟨k, hk⟩ := hnil x
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine mem_of_add_nil J (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1)
    (H * (a x - p x)) _ ?_ k ?_ ?_
  · intro b hb
    apply hreg (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))
    have : p (1 + l * (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))) * b =
        -((((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) * b) := by
      simp only [map_add, map_mul, map_one, map_natCast, map_neg, map_pow, Nat.cast_pow]
      ring
    rw [this]
    exact J.neg_mem hb
  · rw [mul_pow]; exact J.mul_mem_left _ hk
  · have e : p x + (a x - p x) = a x := by ring
    rw [e] at hH
    have : (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1 + H * (a x - p x)) * (a x - p x)
        = (a x ^ (l ^ (d' + 1)) - a x) - (p x ^ (l ^ (d' + 1)) - p x) := by
      rw [hH]; ring
    rw [this]
    exact ht
end GlobalTheory.GenEigen
