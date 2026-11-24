-- Prove2me | solution 1 for GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:19.248806+00:00
-- url     : https://prove2.me/submissions/e13902e7-2f61-4cf5-9285-43143deda024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatSmulLe
import Theorems.Thm_GlobalTheory_NatMultipleIntegralSmulBound_exists_nat_mul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMultipleIntegralSmulBound
open NumberField
namespace GlobalTheory.NatMultipleIntegralSmulBound
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L' : Submodule (RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
  have key : ∀ x ∈ Submodule.span E (↑L' : Set (Fin n → E)), ∃ c : ℕ, 0 < c ∧ (c : E) • x ∈ L' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨d, hd, hdy⟩ := hy
      refine ⟨c * d, Nat.mul_pos hc hd, ?_⟩
      have e : ((c * d : ℕ) : E) • (x + y) = d • ((c : E) • x) + c • ((d : E) • y) := by
        rw [smul_add, ← Nat.cast_smul_eq_nsmul E d, ← Nat.cast_smul_eq_nsmul E c, smul_smul, smul_smul,
          Nat.cast_mul, mul_comm (d : E)]
      rw [e]
      exact L'.add_mem (L'.nsmul_mem hcx d) (L'.nsmul_mem hdy c)
    | smul e x _ hx =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨m, hm, b, hb⟩ := exists_nat_mul_integral e
      refine ⟨m * c, Nat.mul_pos hm hc, ?_⟩
      have e' : ((m * c : ℕ) : E) • (e • x) = (b : E) • ((c : E) • x) := by
        rw [hb, smul_smul, smul_smul, Nat.cast_mul]
        congr 1
        ring
      have hb' : (b : E) • ((c : E) • x) = b • ((c : E) • x) := algebraMap_smul E b _
      rw [e', hb']
      exact L'.smul_mem b hcx
  exact key x (h ▸ Submodule.mem_top)
end GlobalTheory.NatMultipleIntegralSmulBound
