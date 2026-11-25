-- Prove2me | solution 1 for GlobalTheory.SmallIntegerVanishing.eq_zero_of_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:58.111175+00:00
-- url     : https://prove2.me/submissions/9661a417-7393-45e1-8fe9-04825b2b4ca6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SmallIntegerVanishing
namespace GlobalTheory.SmallIntegerVanishing
theorem _root_.solution (E : Type) [Field E] [NumberField E] (x : RingOfIntegers E)
    (h : ∀ w : InfinitePlace E, w (x : E) < 1) : x = 0 := by
  classical
  by_contra hx
  have hnn : ∀ (w : InfinitePlace E) (y : E), 0 ≤ w y := fun w y => w.1.nonneg y
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have h1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : E)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hne
    exact_mod_cast this
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm] at h1
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at h1
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => pow_nonneg (hnn w _) _) fun w _ => pow_le_one₀ (hnn w _) (h w).le
  have hlt : w0 (x : E) ^ w0.mult < 1 :=
    pow_lt_one₀ (hnn w0 _) (h w0) NumberField.InfinitePlace.mult_ne_zero
  have h3 : w0 (x : E) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ w0 (x : E) ^ w0.mult :=
    mul_le_of_le_one_right (pow_nonneg (hnn w0 _) _) hle
  linarith
end GlobalTheory.SmallIntegerVanishing
