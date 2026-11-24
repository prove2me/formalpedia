-- Prove2me | solution 1 for GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:54.515568+00:00
-- url     : https://prove2.me/submissions/980ab4b2-c864-4565-92c7-5a140004a21e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
import Theorems.Thm_GlobalTheory_IntegralMultipleClearDenominators_exists_nat_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultipleClearDenominators
open NumberField
namespace GlobalTheory.IntegralMultipleClearDenominators
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (↑L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hxa b
    · rw [mul_smul]; exact nsmul_mem hyb a
  | smul c x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨K, hK, hint⟩ := exists_nat_mul_integral c
    refine ⟨K * a, Nat.mul_pos hK ha, ?_⟩
    have h := L.smul_mem (⟨(K : E) * c, hint⟩ : RingOfIntegers E) hxa
    convert h using 1
    ext i
    change _ = ((K : E) * c) * (a • x i)
    simp only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
end GlobalTheory.IntegralMultipleClearDenominators
