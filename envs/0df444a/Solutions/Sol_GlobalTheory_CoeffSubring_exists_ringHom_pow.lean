-- Prove2me | solution 1 for GlobalTheory.CoeffSubring.exists_ringHom_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:37.680871+00:00
-- url     : https://prove2.me/submissions/ecddb077-78b9-424c-949f-c366de6701ff

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
theorem _root_.solution
    (hB : ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
      ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b)
    (n : ℕ) (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q) (h : ∀ b ∈ B, g b ^ p ^ n = f b) :
    ∃ σ : k →+* Q, (∀ x, σ (x ^ p ^ n) = f x) ∧ ∀ b ∈ B, σ b = g b := by
  induction n generalizing f with
  | zero => exact ⟨f, by simp, fun b hb => by simpa using (h b hb).symm⟩
  | succ n ih =>
    obtain ⟨σ₁, h1, h2⟩ := hB Q f (fun b => g b ^ p ^ n) fun b hb => by
      rw [← pow_mul, ← pow_succ, h b hb]
    obtain ⟨σ, h3, h4⟩ := ih σ₁ fun b hb => (h2 b hb).symm
    exact ⟨σ, fun x => by rw [pow_succ', pow_mul, h3, h1], h4⟩
end GlobalTheory.CoeffSubring
