-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.closure_pow_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:35.69379+00:00
-- url     : https://prove2.me/submissions/d68c8c24-2b0b-47ac-a462-195487977a08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {k : Type} [Field k] {p : ℕ} {B : Set k}
namespace GlobalTheory.CoeffSubring
theorem _root_.solution (hp : p.Prime) (h0 : (p : k) = 0)
    (hB : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤) (n : ℕ) :
    Subring.closure (Set.range (fun x : k => x ^ p ^ n) ∪ B) = ⊤ := by
  have := Fact.mk hp
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  induction n with
  | zero => exact eq_top_iff.2 fun x _ => Subring.subset_closure (Or.inl ⟨x, by simp⟩)
  | succ n ih =>
    set K := Subring.closure (Set.range (fun x : k => x ^ p ^ (n + 1)) ∪ B)
    have h1 : K.comap (frobenius k p) = ⊤ := by
      rw [eq_top_iff, ← ih, Subring.closure_le]
      rintro _ (⟨x, rfl⟩ | hb)
      · exact Subring.subset_closure (Or.inl ⟨x, by simp [frobenius_def, pow_succ, pow_mul]⟩)
      · exact pow_mem (Subring.subset_closure (Or.inr hb) : _ ∈ K) p
    rw [eq_top_iff, ← hB, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | hb)
    · exact h1.ge (Subring.mem_top x)
    · exact Subring.subset_closure (Or.inr hb)
end GlobalTheory.CoeffSubring
