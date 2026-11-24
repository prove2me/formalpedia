-- Prove2me | solution 1 for GlobalTheory.NatMulIntegral.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:05.793889+00:00
-- url     : https://prove2.me/submissions/fc1b2e41-d6c4-40be-9271-2431ddd89361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNatSmulMem
import Theorems.Thm_GlobalTheory_NatMulIntegral_exists_nat_mul_isIntegral
import Theorems.Thm_GlobalTheory_NatMulIntegral_nat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulIntegral
open NumberField
namespace GlobalTheory.NatMulIntegral
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hez⟩ := hz
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have h1 := nat_smul_mem L e hdx
    have h2 := nat_smul_mem L d hez
    have : ((d * e : ℕ) : E) • (x + z) = (e : E) • (d : E) • x + (d : E) • (e : E) • z := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (e : E)]
    rw [this]
    exact L.add_mem h1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hea⟩ := exists_nat_mul_isIntegral a
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    let b : RingOfIntegers E := ⟨(e : E) * a, hea⟩
    have h1 : b • (d : E) • x ∈ L := L.smul_mem b hdx
    have : ((d * e : ℕ) : E) • a • x = b • (d : E) • x := by
      rw [← algebraMap_smul E b]
      change _ = ((e : E) * a) • (d : E) • x
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact h1
end GlobalTheory.NatMulIntegral
