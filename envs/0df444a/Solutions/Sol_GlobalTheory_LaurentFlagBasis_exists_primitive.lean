-- Prove2me | solution 1 for GlobalTheory.LaurentFlagBasis.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:50:57.117797+00:00
-- url     : https://prove2.me/submissions/aa159433-cba4-4425-a510-74e4b59b39e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory GlobalTheory.LaurentFlagBasis
variable {F : Type} [Field F]
namespace GlobalTheory.LaurentFlagBasis
theorem _root_.solution {n : ℕ} (u : Fin n → LaurentSeries F) (hu : u ≠ 0) :
    ∃ (i : Fin n) (y : Fin n → PowerSeries F), lift y = (u i)⁻¹ • u ∧ y i = 1 := by
  obtain ⟨l, hl⟩ : ∃ l, u l ≠ 0 := by
    by_contra h; push_neg at h; exact hu (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun a => Valued.v (u a))
    ⟨l, Finset.mem_univ _⟩
  have hvl : Valued.v (u l) ≠ 0 := (Valuation.ne_zero_iff _).mpr hl
  have hvi : 0 < Valued.v (u i) := by
    have := hi l (Finset.mem_univ _)
    exact lt_of_lt_of_le (zero_lt_iff.mpr hvl) this
  have hui : u i ≠ 0 := (Valuation.ne_zero_iff _).mp hvi.ne'
  have key : ∀ a, ∃ P : PowerSeries F, (P : LaurentSeries F) = (u i)⁻¹ * u a := by
    intro a
    have := (LaurentSeries.val_le_one_iff_eq_coe F ((u i)⁻¹ * u a)).mp (by
      rw [map_mul, map_inv₀, inv_mul_le_one₀ hvi]
      exact hi a (Finset.mem_univ _))
    exact this
  choose y hy using key
  refine ⟨i, y, funext fun a => ?_, ?_⟩
  · simp [lift, hy]
  · apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change ((y i : PowerSeries F) : LaurentSeries F) = ((1 : PowerSeries F) : LaurentSeries F)
    rw [hy, inv_mul_cancel₀ hui, map_one]
end GlobalTheory.LaurentFlagBasis
