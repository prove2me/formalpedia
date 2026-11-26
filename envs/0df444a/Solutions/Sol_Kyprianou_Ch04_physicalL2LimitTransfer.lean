-- Prove2me | solution 1 for Kyprianou.Ch04.physicalL2LimitTransfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:56:35.239922+00:00
-- url     : https://prove2.me/submissions/faeeccb0-4f74-47fb-901c-860d2b377da7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_l2IsometryLimitTransfer
import Theorems.Thm_Kyprianou_Ch04_lpNormEqOfSquareIntegralEq
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Transfer a physical L2 isometry from an L1-convergent approximation. -/
theorem solution
    {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) (P : Measure Omega)
    (f : ℕ → A → ℝ) (g : A → ℝ)
    (X : ℕ → Omega → ℝ) (Y : Omega → ℝ)
    (hf : ∀ n, MemLp (f n) 2 mu) (hg : MemLp g 2 mu)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hXi : ∀ n, Integrable (X n) P) (hYi : Integrable Y P)
    (hfg : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)))
    (hL1 : Tendsto (fun n => ∫ w, |X n w - Y w| ∂P) atTop (𝓝 0))
    (hSq : ∀ n, (∫ w, (X n w)^2 ∂P) = ∫ a, (f n a)^2 ∂mu)
    (hDiff : ∀ n m, (∫ w, (X n w - X m w)^2 ∂P) =
      ∫ a, (f n a - f m a)^2 ∂mu) :
    MemLp Y 2 P ∧ (∫ w, (Y w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  have he (n : ℕ) : eLpNorm (X n - Y) 1 P =
      ENNReal.ofReal (∫ w, |X n w - Y w| ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    have h := (hXi n).sub hYi
    have heq := integral_norm_eq_lintegral_enorm h.aestronglyMeasurable
    have hfin : (∫⁻ w, ‖(X n - Y) w‖ₑ ∂P) ≠ ⊤ := h.2.ne
    rw [← ENNReal.ofReal_toReal hfin, ← heq]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hY : TendstoInMeasure P X atTop Y := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
      (fun n => (hXi n).aestronglyMeasurable) hYi.aestronglyMeasurable
    simpa only [he, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hL1
  apply Kyprianou.Ch04.l2IsometryLimitTransfer mu P f g X Y hf hg hX hfg hY
  · intro n m
    rw [dist_eq_norm, dist_eq_norm, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
    exact Kyprianou.Ch04.lpNormEqOfSquareIntegralEq mu P
      (f n - f m) (X n - X m) ((hf n).sub (hf m)) ((hX n).sub (hX m)) (hDiff n m)
  · intro n
    exact Kyprianou.Ch04.lpNormEqOfSquareIntegralEq mu P (f n) (X n)
      (hf n) (hX n) (hSq n)
