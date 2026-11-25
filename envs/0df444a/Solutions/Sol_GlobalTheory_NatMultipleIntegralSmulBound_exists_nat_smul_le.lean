-- Prove2me | solution 1 for GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:41.480224+00:00
-- url     : https://prove2.me/submissions/7f0c3dd8-0ec1-4b58-ba1d-7c4ca551023c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNatSmulLe
import Theorems.Thm_GlobalTheory_NatMultipleIntegralSmulBound_exists_nat_smul_mem

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
theorem _root_.solution {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L L' : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.FG L)
    (h : Submodule.span E (↑L' : Set (Fin n → E)) = ⊤) :
    ∃ (c : ℕ), (0 : ℕ) < c ∧ ∀ x ∈ L, (↑c : E) • x ∈ L' := by
  classical
  obtain ⟨s, rfl⟩ := hL
  have hs : ∃ c : ℕ, 0 < c ∧ ∀ x ∈ s, (c : E) • x ∈ L' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert a s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      obtain ⟨d, hd, hda⟩ := exists_nat_smul_mem L' h a
      refine ⟨c * d, Nat.mul_pos hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · have e : ((c * d : ℕ) : E) • x = c • ((d : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E c, smul_smul, Nat.cast_mul]
        rw [e]
        exact L'.nsmul_mem hda c
      · have e : ((c * d : ℕ) : E) • x = d • ((c : E) • x) := by
          rw [← Nat.cast_smul_eq_nsmul E d, smul_smul, Nat.cast_mul, mul_comm]
        rw [e]
        exact L'.nsmul_mem (hcs x hx) d
  obtain ⟨c, hc, hcs⟩ := hs
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hcs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact L'.add_mem hx hy
  | smul b x _ hx =>
    rw [Nat.cast_smul_eq_nsmul] at hx ⊢
    rw [smul_comm]
    exact L'.smul_mem b hx
end GlobalTheory.NatMultipleIntegralSmulBound
