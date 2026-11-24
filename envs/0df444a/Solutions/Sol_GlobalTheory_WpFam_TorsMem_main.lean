-- Prove2me | solution 1 for GlobalTheory.WpFam.TorsMem.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:01.822665+00:00
-- url     : https://prove2.me/submissions/d12cf000-7bd3-4c27-a13d-9452657363be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembership
import Theorems.Thm_GlobalTheory_WpFam_TorsMem_div_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.TorsMem
namespace GlobalTheory.WpFam.TorsMem
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  intro N _ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : ∀ x : Fin 2 → ZMod N,
      tors N τ x = ((((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ)) / N := by
    intro x
    simp only [tors, Int.cast_natCast]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have e : tors N τ x - tors N τ y = (((((x 0).val : ℤ) - (y 0).val : ℤ) : ℂ) * τ
        + ((((x 1).val : ℤ) - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht]; push_cast; ring
    rw [e, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp [sub_eq_zero]
  · intro x y
    have e : tors N τ (x + y) - (tors N τ x + tors N τ y) =
        (((((x + y) 0).val : ℤ) - (x 0).val - (y 0).val : ℤ) * (τ : ℂ)
        + (((((x + y) 1).val : ℤ) - (x 1).val - (y 1).val : ℤ) : ℂ)) / N := by
      rw [ht, ht, ht]; push_cast; ring
    rw [e, div_mem_iff]
    simp
  · intro x
    rw [ht, div_mem_iff, funext_iff, Fin.forall_fin_two]
    simp
  · intro x
    rw [PeriodPair.mem_lattice]
    refine ⟨(x 0).val, (x 1).val, ?_⟩
    change (((x 0).val : ℤ) : ℂ) * τ + (((x 1).val : ℤ) : ℂ) * 1 = _
    rw [ht]
    field_simp
  · intro z hz
    obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hz
    change (m : ℂ) * τ + n * 1 = N * z at h
    refine ⟨![(m : ZMod N), (n : ZMod N)], ?_⟩
    have hz' : z = ((m : ℂ) * τ + (n : ℂ)) / N := by
      rw [eq_div_iff hN]
      linear_combination -h
    have e : z - tors N τ ![(m : ZMod N), (n : ZMod N)] =
        (((m - ((m : ZMod N)).val : ℤ) : ℂ) * τ + ((n - ((n : ZMod N)).val : ℤ) : ℂ)) / N := by
      rw [hz', ht]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring
    rw [e, div_mem_iff]
    simp
end GlobalTheory.WpFam.TorsMem
