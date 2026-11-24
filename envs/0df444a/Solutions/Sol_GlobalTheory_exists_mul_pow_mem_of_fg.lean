-- Prove2me | solution 1 for GlobalTheory.exists_mul_pow_mem_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:45.468417+00:00
-- url     : https://prove2.me/submissions/b38b0607-573a-45df-a2f3-b3a40adaa7a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsRingHomOfMulPowMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (A B : Subalgebra O Ω) (hA : A.FG)
    (hB : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) :
    ∃ d ∈ B, d ≠ 0 ∧ ∀ a ∈ A, ∃ n : ℕ, a * d ^ n ∈ B := by
  classical
  obtain ⟨s, hs⟩ := hA
  have hden : ∀ x : Ω, ∃ b ∈ B, b ≠ 0 ∧ x * b ∈ B := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hB x
    exact ⟨b, hb, hb0, by rw [hx]; exact ha⟩
  choose den hdenB hden0 hdenmul using hden
  have hD : ∏ x ∈ s, den x ∈ B := Subalgebra.prod_mem B (fun x _ => hdenB x)
  refine ⟨∏ x ∈ s, den x, hD, Finset.prod_ne_zero_iff.mpr (fun x _ => hden0 x), ?_⟩
  intro a ha
  rw [← hs] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>

    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.mul_prod_erase s den (Finset.mem_coe.mp hx), ← mul_assoc]
    exact mul_mem (hdenmul x) (Subalgebra.prod_mem B (fun y _ => hdenB y))
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : (x + y) * (∏ z ∈ s, den z) ^ (n + m) =
        x * (∏ z ∈ s, den z) ^ n * (∏ z ∈ s, den z) ^ m +
          y * (∏ z ∈ s, den z) ^ m * (∏ z ∈ s, den z) ^ n := by ring
    rw [e]
    exact add_mem (mul_mem hn (pow_mem hD m)) (mul_mem hm (pow_mem hD n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : x * y * (∏ z ∈ s, den z) ^ (n + m) =
        (x * (∏ z ∈ s, den z) ^ n) * (y * (∏ z ∈ s, den z) ^ m) := by ring
    rw [e]
    exact mul_mem hn hm
end GlobalTheory
