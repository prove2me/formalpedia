-- Prove2me | solution 1 for GlobalTheory.StdChar.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:10:56.19693+00:00
-- url     : https://prove2.me/submissions/c782ae49-f7e8-4a31-8866-5e25632edfa4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Theorems.Thm_GlobalTheory_StdChar_exists_nat_norm_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
variable {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.StdChar
theorem _root_.solution [IsUltrametricDist F] [ProperSpace F] [CharZero F] {ψ : AddChar F ℂ}
    (hψ : IsStdChar ψ) (x : F) : ‖ψ x‖ = 1 := by
  obtain ⟨N, hN0, hN1⟩ := exists_nat_norm_lt_one (F := F)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hxpos) hN1
  have h1 : ψ ((N ^ k : ℕ) • x) = 1 := by
    apply hψ.1
    rw [nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]
    exact (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)).trans (by rw [inv_mul_cancel₀ hxpos.ne'])
  rw [AddChar.map_nsmul_eq_pow] at h1
  have h2 : ‖ψ x‖ ^ (N ^ k) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hN0.ne')).1 h2
end GlobalTheory.StdChar
