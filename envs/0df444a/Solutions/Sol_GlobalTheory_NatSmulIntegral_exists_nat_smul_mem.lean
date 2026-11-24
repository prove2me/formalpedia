-- Prove2me | solution 1 for GlobalTheory.NatSmulIntegral.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:23:01.816059+00:00
-- url     : https://prove2.me/submissions/2c5ea377-1ecf-492b-aa00-524ea4e12d2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ImportsTer
import Theorems.Thm_GlobalTheory_NatSmulIntegral_exists_nat_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatSmulIntegral
open NumberField
namespace GlobalTheory.NatSmulIntegral
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ N : ℕ, 0 < N ∧ N • y ∈ L := by
  have hy : y ∈ Submodule.span E (↑L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  have key : ∀ c : E, ∃ N : ℕ, 0 < N ∧ N • (c • y) ∈ L := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      intro c
      obtain ⟨N, hN, a, ha⟩ := exists_nat_mul_integral c
      refine ⟨N, hN, ?_⟩
      have h1 : N • (c • x) = a • x := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, ← ha]
        rfl
      rw [h1]
      exact L.smul_mem a hx
    | zero => intro c; exact ⟨1, one_pos, by simp⟩
    | add x y _ _ ihx ihy =>
      intro c
      obtain ⟨N, hN, h1⟩ := ihx c
      obtain ⟨M, hM, h2⟩ := ihy c
      refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
      rw [smul_add, smul_add]
      refine L.add_mem ?_ ?_
      · rw [mul_smul]; exact nsmul_mem h1 M
      · rw [mul_comm, mul_smul]; exact nsmul_mem h2 N
    | smul a x _ ih =>
      intro c
      rw [smul_smul]
      exact ih _
  simpa using key 1
end GlobalTheory.NatSmulIntegral
