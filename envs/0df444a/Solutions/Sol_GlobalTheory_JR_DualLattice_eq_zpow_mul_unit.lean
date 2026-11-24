-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.eq_zpow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:35.776732+00:00
-- url     : https://prove2.me/submissions/8b9d6cb4-f49a-4d55-8850-50b18d7423b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianTraceDualIntegersEqUniformizerPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
variable {R : Type} [CommRing R]
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution (O : Subring R) (p : Rˣ)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = (p : R) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hsep : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ≠ x)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O) :
    ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u := by
  classical
  have hO : ∀ x ∈ O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ x = (p : R) ^ k * u := by
    intro x hxO hx0
    have hex' : ∃ k : ℕ, ¬ ∃ z ∈ O, x = (p : R) ^ k * z := by
      obtain ⟨n, hn⟩ := hsep x hx0
      exact ⟨n, fun ⟨z, hz, hzx⟩ => hn z hz hzx.symm⟩
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, (¬ ∃ z ∈ O, x = (p : R) ^ m * z) ∧
        ∀ j < m, ∃ z ∈ O, x = (p : R) ^ j * z :=
      ⟨Nat.find hex', Nat.find_spec hex', fun j hj => by simpa using Nat.find_min hex' hj⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm ⟨x, hxO, by simp⟩
    obtain ⟨z, hz, hxz⟩ := hmin (m - 1) (by omega)
    rcases hdich z hz with ⟨w, hw, hzw⟩ | hu
    · exfalso
      apply hm
      refine ⟨w, hw, ?_⟩
      rw [hxz, hzw, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    · exact ⟨_, z, hz, hu, hxz⟩
  intro y hy
  obtain ⟨n, hn⟩ := hex y
  have hne : (p : R) ^ n * y ≠ 0 := by
    intro h
    apply hy
    have := congrArg (fun t => ((p⁻¹ : Rˣ) : R) ^ n * t) h
    simpa [← mul_assoc, ← mul_pow] using this
  obtain ⟨k, u, hu, hunit, hk⟩ := hO _ hn hne
  refine ⟨(k : ℤ) - n, u, hu, hunit, ?_⟩
  have e1 : ((p ^ ((k : ℤ) - n) : Rˣ) : R) = ((p⁻¹ : Rˣ) : R) ^ n * (p : R) ^ k := by
    rw [_root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, mul_comm]
  rw [e1, mul_assoc, ← hk, ← mul_assoc, ← mul_pow]
  simp
end GlobalTheory.JR.DualLattice
