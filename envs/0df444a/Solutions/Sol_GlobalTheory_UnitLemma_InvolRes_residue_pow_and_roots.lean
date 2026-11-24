-- Prove2me | solution 1 for GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:59:01.771863+00:00
-- url     : https://prove2.me/submissions/176462cd-6cec-436f-af69-11b35567dcdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnity
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_invol_eq_pow
import Theorems.Thm_GlobalTheory_UnitLemma_UnrExt_root_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.InvolRes
namespace GlobalTheory.UnitLemma.InvolRes
theorem _root_.solution : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ),
    Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) →
    (∃ x, residue S (τ x) ≠ residue S x) →
    (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  intro S _ _ _ M hM τ hττ hne
  let e : S ≃+* S := RingEquiv.ofRingHom τ τ (RingHom.ext hττ) (RingHom.ext hττ)
  let s := ResidueField.mapEquiv e
  have hs : ∀ x, s (residue S x) = residue S (τ x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  haveI := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField S) p⟩
  obtain ⟨-, hsq⟩ := GlobalTheory.UnitLemma.UnrExt.invol_eq_pow p hM s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hττ]) (by
    obtain ⟨x, hx⟩ := hne
    exact ⟨residue S x, by rw [hs]; exact hx⟩)
  have h1 : ∀ x, residue S (τ x) = residue S x ^ M := fun x => by rw [← hs, hsq]
  refine ⟨h1, fun w hw => ?_⟩
  have hcard2 : 2 ≤ M ^ 2 := by
    have : 1 < Nat.card (ResidueField S) := Finite.one_lt_card
    omega
  set N := M ^ 2 - 1 with hN
  have hNk : (N : ResidueField S) ≠ 0 := by
    haveI := Fintype.ofFinite (ResidueField S)
    have h0 : ((N + 1 : ℕ) : ResidueField S) = 0 := by
      rw [show N + 1 = M ^ 2 by omega, ← hM, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h0
  refine GlobalTheory.UnitLemma.UnrExt.root_unique (residue S) (ker_residue) (X ^ N - 1 : S[X])
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) (a := τ w) (b := w ^ M) ?_ ?_ ?_
  · simp [← map_pow, hw]
  · simp only [eval_sub, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow, sub_self]
  · rw [h1, map_pow]
end GlobalTheory.UnitLemma.InvolRes
