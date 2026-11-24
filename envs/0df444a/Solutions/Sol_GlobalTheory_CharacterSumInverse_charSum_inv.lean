-- Prove2me | solution 1 for GlobalTheory.CharacterSumInverse.charSum_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:49.12335+00:00
-- url     : https://prove2.me/submissions/d0f2faf3-06df-4bae-964e-73daa35065da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharacterSumInverse
open scoped BigOperators
namespace GlobalTheory.CharacterSumInverse
theorem _root_.solution {o : Type} [CommRing o] [IsDomain o] {T : Type} [CommGroup T] [Fintype T]
    [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)] [DecidableEq T] (t : T) :
    (∑ c : T →* oˣ, ((c t)⁻¹ : oˣ).val) = if t = 1 then (Fintype.card T : o) else 0 := by
  classical
  have hinv : ∀ c : T →* oˣ, ((c t)⁻¹ : oˣ).val = (c t⁻¹).val := fun c => by rw [map_inv]
  simp_rw [hinv]
  split_ifs with ht
  · subst ht
    simp only [inv_one, map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    have h := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T o
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [h]
  · have hs : t⁻¹ ≠ 1 := by simpa using ht
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity T o hs
    set S := ∑ c : T →* oˣ, (c t⁻¹).val with hS
    have hshift : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = S :=
      Fintype.sum_equiv (Equiv.mulLeft φ) _ _ (fun _ => rfl)
    have hmul : (∑ c : T →* oˣ, ((φ * c) t⁻¹).val) = (φ t⁻¹).val * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp [MonoidHom.mul_apply, Units.val_mul]
    have h0 : ((φ t⁻¹).val - 1) * S = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    have hne : (φ t⁻¹).val - 1 ≠ 0 := by
      intro h
      apply hφ
      exact Units.val_eq_one.mp (sub_eq_zero.mp h)
    exact (mul_eq_zero.mp h0).resolve_left hne
end GlobalTheory.CharacterSumInverse
