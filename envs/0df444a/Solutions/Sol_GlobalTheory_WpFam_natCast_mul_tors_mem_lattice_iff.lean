-- Prove2me | solution 1 for GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:15.811981+00:00
-- url     : https://prove2.me/submissions/2baa9cbc-ef55-45ae-9e4e-e74485b0b5eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastMulTorsMemLatticeIff
import Theorems.Thm_GlobalTheory_WpFam_nsmul_zmod_eq_zero_iff_dvd

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
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution :
    ∀ (N : ℕ) [NeZero N] (τ : ℍ) (M : ℕ) (x : Fin 2 → ZMod N),
      (M : ℂ) * tors N τ x ∈ (tauPair τ).lattice ↔ M • x = 0 := by
  intro N _ τ M x
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hx : M • x = 0 ↔ N ∣ M * (x 0).val ∧ N ∣ M * (x 1).val := by
    rw [← nsmul_zmod_eq_zero_iff_dvd, ← nsmul_zmod_eq_zero_iff_dvd, funext_iff, Fin.forall_fin_two]
    rfl
  have hm : ∀ z : ℂ, z ∈ (tauPair τ).lattice ↔ ∃ m n : ℤ, m * (τ : ℂ) + n = z := by
    intro z
    rw [PeriodPair.mem_lattice]; simp [tauPair]
  rw [hx, hm]
  constructor
  · rintro ⟨m, n, h⟩
    have h1 : ((N * m - M * (x 0).val : ℤ) : ℂ) * (τ : ℂ) + ((N * n - M * (x 1).val : ℤ) : ℂ) = 0 := by
      unfold tors at h
      field_simp at h
      push_cast
      linear_combination h
    have him := congrArg Complex.im h1
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero,
      Complex.zero_im, UpperHalfPlane.coe_im, mul_eq_zero, τ.im_pos.ne', or_false, Int.cast_eq_zero] at him
    rw [him, Int.cast_zero, zero_mul, zero_add, Int.cast_eq_zero] at h1
    constructor
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨m, by push_cast at him ⊢; linear_combination -him⟩
    · rw [← Int.natCast_dvd_natCast]
      exact ⟨n, by push_cast at h1 ⊢; linear_combination -h1⟩
  · rintro ⟨⟨m, hm0⟩, ⟨n, hn0⟩⟩
    refine ⟨m, n, ?_⟩
    have a : (M : ℂ) * ((x 0).val : ℂ) = N * m := by exact_mod_cast hm0
    have b : (M : ℂ) * ((x 1).val : ℂ) = N * n := by exact_mod_cast hn0
    unfold tors
    field_simp
    push_cast
    linear_combination -(τ : ℂ) * a - b
end GlobalTheory.WpFam
