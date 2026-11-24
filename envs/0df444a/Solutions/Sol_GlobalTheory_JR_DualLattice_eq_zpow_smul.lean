-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.eq_zpow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:36.647578+00:00
-- url     : https://prove2.me/submissions/cb54bcf3-6bd3-4c17-a2e2-0798f64e25ff

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
theorem _root_.solution (O : Subring R) (p : Rˣ) (D : Set R) (hpO : (p : R) ∈ O)
    (hmul : ∀ y ∈ D, ∀ r ∈ O, r * y ∈ D)
    (hbig : ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ∈ D)
    (hne : ∃ y, y ∉ D)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O)
    (hunit : ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u) :
    ∃ e : ℤ, D = {y | ∃ z ∈ O, y = ((p ^ e : Rˣ) : R) * z} := by
  classical
  have hup : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → ∀ k : ℕ, ((p ^ (v + k) : Rˣ) : R) ∈ D := by
    intro v hv k
    have : ((p ^ (v + k) : Rˣ) : R) = (p : R) ^ k * ((p ^ v : Rˣ) : R) := by
      rw [_root_.zpow_add, zpow_natCast, mul_comm, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this]
    exact hmul _ hv _ (pow_mem hpO k)
  obtain ⟨n, hn⟩ := hbig
  have hinh : ∃ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := ⟨n, by simpa using hn 1 (one_mem O)⟩
  have hbdd : ∃ b : ℤ, ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → b ≤ v := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := by
      intro v
      obtain ⟨w, hw, hwv⟩ := hcon v
      have := hup w hw (v - w).toNat
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
    obtain ⟨y, hy⟩ := hne
    obtain ⟨m, hm⟩ := hex y
    apply hy
    have h1 := hmul _ (hall (-(m : ℤ))) _ hm
    have hq : ((p ^ (-(m : ℤ)) : Rˣ) : R) * (p : R) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
        neg_add_cancel, zpow_zero, Units.val_one]
    have h2 : (p : R) ^ m * y * ((p ^ (-(m : ℤ)) : Rˣ) : R) = y := by
      linear_combination y * hq
    rwa [h2] at h1
  obtain ⟨e, he, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨e, Set.ext fun y => ⟨fun hy => ?_, fun ⟨z, hz, hyz⟩ => ?_⟩⟩
  · by_cases hy0 : y = 0
    · exact ⟨0, zero_mem O, by simp [hy0]⟩
    obtain ⟨v, u, hu, ⟨w, hw, huw⟩, hyv⟩ := hunit y hy0
    have hv : ((p ^ v : Rˣ) : R) ∈ D := by
      have := hmul y hy w hw
      have e2 : w * y = ((p ^ v : Rˣ) : R) := by rw [hyv, mul_comm, mul_assoc, huw, mul_one]
      rwa [e2] at this
    have hev := hmin v hv
    refine ⟨(p : R) ^ (v - e).toNat * u, O.mul_mem (pow_mem hpO _) hu, ?_⟩
    rw [hyv, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
      Int.toNat_of_nonneg (by omega), add_sub_cancel]
  · rw [hyz, mul_comm]
    exact hmul _ he _ hz
end GlobalTheory.JR.DualLattice
