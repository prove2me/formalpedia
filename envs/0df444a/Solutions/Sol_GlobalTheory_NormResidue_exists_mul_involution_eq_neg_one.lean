-- Prove2me | solution 1 for GlobalTheory.NormResidue.exists_mul_involution_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:44.880817+00:00
-- url     : https://prove2.me/submissions/ce307797-98dd-490c-9a68-153863e60a6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsMulInvolutionAddOneMemPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormResidue
open Polynomial
namespace GlobalTheory.NormResidue
theorem _root_.solution {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (h2 : (2 : k) ≠ 0) :
    ∃ z : k, z * σ z + 1 = 0 := by
  classical
  obtain ⟨x, hx⟩ := hne
  let F : Subfield k := σ.eqLocusField (RingHom.id k)
  let _ : Fintype F := Fintype.ofFinite F
  have memF : ∀ y : k, y ∈ F ↔ σ y = y := fun y => Iff.rfl
  have hθ : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ]; ring
  have hθ0 : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let d : F := ⟨(x - σ x) * (x - σ x), (memF _).2 (by rw [map_mul, hθ]; ring)⟩
  have hd0 : d ≠ 0 := by
    intro h
    have h' : (x - σ x) * (x - σ x) = 0 := congrArg Subtype.val h
    exact hθ0 (mul_self_eq_zero.mp h')
  have hchar : ringChar F ≠ 2 := by
    intro hc
    apply h2
    have h0 : ((2 : ℕ) : F) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h0' := congrArg F.subtype h0
    rwa [map_natCast, map_zero, Nat.cast_ofNat] at h0'
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) _)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd0))
    (FiniteField.odd_card_of_char_ne_two hchar)
  have hab' := congrArg Subtype.val hab
  simp [d] at hab'
  have ha : σ a = a := (memF _).1 a.2
  have hb : σ b = b := (memF _).1 b.2
  refine ⟨a + b * (x - σ x), ?_⟩
  rw [map_add, map_mul, ha, hb, hθ]
  linear_combination hab'
end GlobalTheory.NormResidue
