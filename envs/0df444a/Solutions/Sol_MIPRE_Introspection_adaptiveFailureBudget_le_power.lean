-- Prove2me | solution 1 for MIPRE.Introspection.adaptiveFailureBudget_le_power
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:58.701684+00:00
-- url     : https://prove2.me/submissions/41723b75-3b81-4bba-937d-c0e1da486990

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean (solution of MIPRE.Introspection.adaptiveFailureBudget_le_power);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget
import Theorems.Thm_MIPRE_Introspection_adaptiveStepLoss_le_root

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection
section
theorem adaptiveStepLoss_mono {δ η : ℝ} (h : δ ≤ η) :
    adaptiveStepLoss δ ≤ adaptiveStepLoss η := by
  unfold adaptiveStepLoss
  gcongr
end
end MIPRE.Introspection

namespace MIPRE.Introspection
section
theorem adaptiveFailureBudget_step (r n : ℕ) (edges z h initial : ℝ) :
    adaptiveFailureBudget r edges z h initial (n + 1) =
      adaptiveFailureBudget r edges z h initial n +
        adaptiveStepLoss (adaptiveStageBudget r
          (edges * adaptiveFailureBudget r edges z h initial n) z h) := rfl
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveStageBudget_mono_errors (r : ℕ)
    {e e' z z' h h' : ℝ} (he : e ≤ e') (hz : z ≤ z') (hh : h ≤ h') :
    adaptiveStageBudget r e z h ≤ adaptiveStageBudget r e' z' h' := by
  unfold adaptiveStageBudget
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (by norm_num))
    (mul_le_mul_of_nonneg_left he (by positivity)))
    (mul_le_mul_of_nonneg_left hh (by norm_num))
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveBudgetCoefficient_pos (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    0 < adaptiveBudgetCoefficient r edges := by
  unfold adaptiveBudgetCoefficient
  positivity
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveStageBudget_le_coefficient (r : ℕ) {edges f z h t : ℝ}
    (hE : 0 ≤ edges) (hf : f ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveStageBudget r (edges * f) z h ≤ adaptiveBudgetCoefficient r edges * t := by
  calc
    _ ≤ adaptiveStageBudget r (edges * t) t t :=
      adaptiveStageBudget_mono_errors r (mul_le_mul_of_nonneg_left hf hE) hz hh
    _ = _ := by unfold adaptiveStageBudget adaptiveBudgetCoefficient; ring
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ iteratedRoot n t := by
  cases n with
  | zero => exact ht
  | succ n => exact Real.sqrt_nonneg _
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_mono (n : ℕ) : Monotone (iteratedRoot n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun _ _ h => Real.sqrt_le_sqrt (ih h)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_one (n : ℕ) : iteratedRoot n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedRoot, ih, Real.sqrt_one]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_le_one (n : ℕ) {t : ℝ} (ht : t ≤ 1) :
    iteratedRoot n t ≤ 1 := by
  simpa only [iteratedRoot_one] using iteratedRoot_mono n ht
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem iteratedRoot_add (m n : ℕ) (t : ℝ) :
    iteratedRoot (m + n) t = iteratedRoot m (iteratedRoot n t) := by
  induction m with
  | zero => simp only [Nat.zero_add, iteratedRoot]
  | succ m ih => simp only [Nat.succ_add, iteratedRoot, ih]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem self_le_iteratedRoot (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ≤ iteratedRoot n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact ih.trans (self_le_sqrt_of_unit (iteratedRoot_nonneg n ht0)
      (iteratedRoot_le_one n ht1))
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
/-- A coefficient at least one can be kept unchanged through any fixed
stack of square roots, which is convenient for explicit uniform constants. -/
theorem iteratedRoot_scale_le (n : ℕ) {c t : ℝ} (hc : 1 ≤ c) :
    iteratedRoot n (c * t) ≤ c * iteratedRoot n t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (Real.sqrt_le_sqrt ih).trans (sqrt_scale_le hc)
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptiveBudgetCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptiveBudgetCoefficient r edges := by
  have hm : 0 ≤ (512 * (r : ℝ) ^ 2 + 224) * edges := by positivity
  unfold adaptiveBudgetCoefficient
  linarith
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
theorem adaptivePowerCoefficient_one_le (r : ℕ) {edges : ℝ} (hE : 0 ≤ edges) :
    1 ≤ adaptivePowerCoefficient r edges := by
  unfold adaptivePowerCoefficient
  linarith [adaptiveBudgetCoefficient_pos r hE]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
theorem _root_.solution (r n : ℕ) {edges z h initial t : ℝ}
    (hE : 0 ≤ edges) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveFailureBudget r edges z h initial n ≤
      adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by
  have hC := adaptiveBudgetCoefficient_one_le r hE
  have hK := adaptivePowerCoefficient_one_le r hE
  induction n with
  | zero => simpa only [adaptiveFailureBudget, pow_zero, Nat.mul_zero,
      iteratedRoot, one_mul] using hi
  | succ n ih =>
    have hKn : 1 ≤ adaptivePowerCoefficient r edges ^ n := one_le_pow₀ hK
    have hKn0 : 0 ≤ adaptivePowerCoefficient r edges ^ n := by linarith
    have hRn0 := iteratedRoot_nonneg (3 * n) ht0
    have hRn1 := iteratedRoot_le_one (3 * n) ht1
    have htR : t ≤ adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by
      calc
        t ≤ iteratedRoot (3 * n) t := self_le_iteratedRoot _ ht0 ht1
        _ ≤ adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hKn) hRn0]
    have hb := adaptiveStageBudget_le_coefficient r hE ih (hz.trans htR) (hh.trans htR)
    have hCK : 1 ≤ adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n :=
          mul_le_mul hC hKn (by norm_num) (by linarith)
    have hs := iteratedRoot_scale_le 3
      (t := iteratedRoot (3 * n) t) hCK
    have hl := (adaptiveStepLoss_mono hb).trans
      (adaptiveStepLoss_le_root
        (adaptiveBudgetCoefficient r edges *
          (adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t)))
    have hl' : adaptiveStepLoss (adaptiveStageBudget r
        (edges * adaptiveFailureBudget r edges z h initial n) z h) ≤
        8 * (adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n) *
          iteratedRoot 3 (iteratedRoot (3 * n) t) := by
      apply hl.trans
      have hmul := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 8)
      simpa only [mul_assoc] using hmul
    have hpre := ih.trans (mul_le_mul_of_nonneg_left
      (self_le_iteratedRoot 3 hRn0 hRn1) hKn0)
    have he : iteratedRoot (3 * (n + 1)) t = iteratedRoot 3 (iteratedRoot (3 * n) t) := by
      rw [show 3 * (n + 1) = 3 + 3 * n by omega, iteratedRoot_add]
    rw [adaptiveFailureBudget_step]
    calc
      _ ≤ adaptivePowerCoefficient r edges ^ n * iteratedRoot 3 (iteratedRoot (3 * n) t) +
          8 * (adaptiveBudgetCoefficient r edges * adaptivePowerCoefficient r edges ^ n) *
            iteratedRoot 3 (iteratedRoot (3 * n) t) := add_le_add hpre hl'
      _ = _ := by rw [he, pow_succ]; unfold adaptivePowerCoefficient; ring
end MIPRE.Introspection
