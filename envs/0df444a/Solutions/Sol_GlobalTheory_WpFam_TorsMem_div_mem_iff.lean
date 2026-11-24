-- Prove2me | solution 1 for GlobalTheory.WpFam.TorsMem.div_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:44.069248+00:00
-- url     : https://prove2.me/submissions/dd66df4a-572b-4766-931e-d7aeb0fc1fc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembership
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
namespace GlobalTheory.WpFam.TorsMem
private theorem div_N_mem_tauPair_lattice_iff_dvd (N : ℕ) [NeZero N] (τ : ℍ) (a b : ℤ) :
    ((a : ℂ) * τ + (b : ℂ)) / N ∈ (tauPair τ).lattice ↔ (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    rw [h1, h2, eq_div_iff hN] at h
    obtain ⟨k1, k2⟩ := LinearIndependent.pair_iff.mp (tauPair τ).indep
      (((N : ℤ) * m - a : ℤ) : ℝ) (((N : ℤ) * n - b : ℤ) : ℝ) (by
        rw [h1, h2, Complex.real_smul, Complex.real_smul]
        push_cast
        linear_combination h)
    norm_cast at k1 k2
    exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    rw [h1, h2, eq_div_iff hN]
    push_cast
    ring
end GlobalTheory.WpFam.TorsMem
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.TorsMem
namespace GlobalTheory.WpFam.TorsMem
theorem _root_.solution (N : ℕ) [NeZero N] (τ : ℍ) (u v : ℤ) :
    ((u : ℂ) * τ + (v : ℂ)) / N ∈ (tauPair τ).lattice ↔ (u : ZMod N) = 0 ∧ (v : ZMod N) = 0 := by
  rw [div_N_mem_tauPair_lattice_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
end GlobalTheory.WpFam.TorsMem
