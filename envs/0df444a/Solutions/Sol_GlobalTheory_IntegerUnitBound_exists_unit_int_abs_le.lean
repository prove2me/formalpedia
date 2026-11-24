-- Prove2me | solution 1 for GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:14.104873+00:00
-- url     : https://prove2.me/submissions/1994ccd0-edc2-4ea7-a684-891701aa0a61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitOfSumEqZero
import Theorems.Thm_GlobalTheory_IntegerUnitBound_exists_unit_of_sum_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open GlobalTheory GlobalTheory.IntegerUnitBound
namespace GlobalTheory.IntegerUnitBound
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by
  classical
  obtain ⟨C, hC⟩ := exists_unit_of_sum_eq_zero E
  refine ⟨C + 1, fun t => ?_⟩

  have hmpos : 0 < ∑ w : InfinitePlace E, (mult w : ℝ) :=
    Finset.sum_pos (fun w _ => Nat.cast_pos.2 mult_pos) Finset.univ_nonempty
  set s : ℝ := (∑ w : InfinitePlace E, (mult w : ℝ) * t w) / ∑ w : InfinitePlace E, (mult w : ℝ) with hs
  have hms : (∑ w : InfinitePlace E, (mult w : ℝ)) * s = ∑ w : InfinitePlace E, (mult w : ℝ) * t w := by
    rw [hs]
    field_simp
  have hsum : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w - s) = 0 := by
    rw [Finset.sum_congr rfl fun w _ => mul_sub (mult w : ℝ) (t w) s, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hms, sub_self]
  obtain ⟨u, hu⟩ := hC (fun w => t w - s) hsum

  refine ⟨u, -⌊s⌋, fun w => ?_⟩
  have h1 := abs_le.1 (hu w)
  have h2 := Int.fract_nonneg s
  have h3 := Int.fract_lt_one s
  have hcoe : algebraMap (𝓞 E) E (u : 𝓞 E) = (u : E) := rfl
  have heq : t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + ((-⌊s⌋ : ℤ) : ℝ) =
      (t w - s + Real.log (w (u : E))) + Int.fract s := by
    rw [hcoe, Int.fract]
    push_cast
    ring
  rw [heq, abs_le]
  constructor <;> linarith [h1.1, h1.2]
end GlobalTheory.IntegerUnitBound
