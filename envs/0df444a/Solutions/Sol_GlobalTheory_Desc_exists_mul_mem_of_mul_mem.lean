-- Prove2me | solution 1 for GlobalTheory.Desc.exists_mul_mem_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:18.038801+00:00
-- url     : https://prove2.me/submissions/836cf1ad-3d2b-4027-bb71-33acac6f3e32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteTypeAwayOfAtPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Desc
open scoped TensorProduct
namespace GlobalTheory.Desc
theorem _root_.solution {R C : Type} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    (B : Subalgebra R C) [IsNoetherianRing B] (x : C) (hx : x ≠ 0) (M : Submonoid R)
    (h : ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ B) :
    ∃ g ∈ M, ∀ c : C, x * c ∈ B → algebraMap R C g * c ∈ B := by
  classical
  let J : Ideal B := (Ideal.span {x}).comap B.val
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  choose r hrM hr using h
  have hJ : ∀ b : B, ∃ c : C, b ∈ J → (b : C) = x * c := by
    intro b
    by_cases hb : b ∈ J
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
      exact ⟨c, fun _ => by rw [mul_comm]; exact hc.symm⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose q hq using hJ
  refine ⟨∏ b ∈ t, r (q b), prod_mem fun b _ => hrM _, ?_⟩
  set g := ∏ b ∈ t, r (q b) with hg
  have key : ∀ b ∈ Ideal.span (t : Set B), ∃ c : C, (b : C) = x * c ∧ algebraMap R C g * c ∈ B := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine ⟨q b, hq b (ht ▸ Ideal.subset_span hb), ?_⟩
      rw [hg, ← Finset.prod_erase_mul t _ hb, map_mul, mul_assoc]
      exact mul_mem (B.algebraMap_mem _) (hr _)
    | zero => exact ⟨0, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, e, hc⟩ := hy
      obtain ⟨d, e', hd⟩ := hz
      exact ⟨c + d, by rw [mul_add, ← e, ← e']; rfl, by rw [mul_add]; exact add_mem hc hd⟩
    | smul a y _ hy =>
      obtain ⟨c, e, hc⟩ := hy
      refine ⟨a * c, by rw [mul_left_comm, ← e]; rfl, ?_⟩
      rw [mul_left_comm]
      exact mul_mem a.2 hc
  intro c hc
  obtain ⟨d, e, hd⟩ := key ⟨x * c, hc⟩ (by
    rw [ht]
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
  rw [mul_left_cancel₀ hx e]
  exact hd
end GlobalTheory.Desc
