-- Prove2me | solution 1 for GlobalTheory.DetInv.mu_coeff_zero_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:42.880099+00:00
-- url     : https://prove2.me/submissions/55a21b24-fbac-48f6-8a98-add917958029

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MuCoeffZeroNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv
open Matrix TensorProduct
namespace GlobalTheory.DetInv
namespace _root_.GlobalTheory.DetInv
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
      (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 ∧
        _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ ε hζ
  have hε : ε ≠ 1 := by
    rintro rfl
    have h1 : _root_.GlobalTheory.Sandwich.root (1 : PreTilt O p) = 1 := by
      unfold _root_.GlobalTheory.Sandwich.root
      exact map_one _
    have h2 : PreTilt.untilt (1 : PreTilt O p) = 1 := by simp
    rw [h1, h2] at hζ
    have hp : p ∣ 1 := (hζ.pow_eq_one_iff_dvd 1).mp (pow_one 1)
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hp)
  have hc : (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 := by
    unfold _root_.GlobalTheory.Sandwich.mu
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr hε
  have hmu : _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
    intro h
    apply hc
    rw [h]
    exact WittVector.zero_coeff _ _ _
  refine ⟨hc, hmu, fun h => hmu ?_⟩
  rw [← _root_.GlobalTheory.Sandwich.xi_mul_nu, h, mul_zero]
end _root_.GlobalTheory.DetInv
end GlobalTheory.DetInv
