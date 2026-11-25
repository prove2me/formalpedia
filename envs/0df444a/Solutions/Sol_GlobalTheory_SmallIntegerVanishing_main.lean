-- Prove2me | solution 1 for GlobalTheory.SmallIntegerVanishing.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:23.153343+00:00
-- url     : https://prove2.me/submissions/7aafdefc-d659-4b0c-a93a-6d968fce083b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsLast
import Theorems.Thm_GlobalTheory_SmallIntegerVanishing_eq_zero_of_small
import Theorems.Thm_GlobalTheory_SmallIntegerVanishing_exists_denominator

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ,
      (∀ (w : InfinitePlace E) (a : Fin j), w (y a) < δ) → y = 0 := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_denominator E j Λ hΛ
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hnn : ∀ (w : InfinitePlace E) (z : E), 0 ≤ w z := fun w z => w.1.nonneg z
  set M : ℝ := ∑ w : InfinitePlace E, w (d : E) with hM
  have hwM : ∀ w : InfinitePlace E, w (d : E) ≤ M := fun w =>
    Finset.single_le_sum (f := fun w : InfinitePlace E => w (d : E)) (fun w _ => hnn w _) (Finset.mem_univ w)
  have hMpos : 0 < M := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    exact lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hdE) (hwM w0)
  refine ⟨1 / M, by positivity, fun y hy hsmall => ?_⟩
  funext a
  obtain ⟨x, hx⟩ := hd y hy a
  have hx0 : x = 0 := eq_zero_of_small E x fun w => by
    rw [hx, map_mul]
    calc w (d : E) * w (y a) ≤ M * w (y a) := mul_le_mul_of_nonneg_right (hwM w) (hnn w _)
      _ < M * (1 / M) := mul_lt_mul_of_pos_left (hsmall w a) hMpos
      _ = 1 := by field_simp
  have hza : (d : E) * y a = 0 := by rw [← hx, hx0]; rfl
  simpa [hdE] using hza
end GlobalTheory.SmallIntegerVanishing
