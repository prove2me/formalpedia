-- Prove2me | solution 1 for Kyprianou.Ch04.physicalL1BoundCongrAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:22:35.984272+00:00
-- url     : https://prove2.me/submissions/f8a99700-0204-4925-80dd-02388be6734e

import Mathlib
open MeasureTheory Filter
set_option autoImplicit false

/-- A physical L1 bound transfers almost-everywhere equality of kernels. -/
theorem solution {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) (P : Measure Omega)
    (f g : A → ℝ) (X Y : Omega → ℝ)
    (hfg : f =ᵐ[mu] g) (hX : Integrable X P) (hY : Integrable Y P)
    (hbound : (∫ w, |X w - Y w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu) :
    X =ᵐ[P] Y := by
  have h0 : (fun a => |f a - g a|) =ᵐ[mu] (fun _ => (0 : ℝ)) := by
    filter_upwards [hfg] with a ha
    simp [ha]
  rw [integral_congr_ae h0, integral_zero, mul_zero] at hbound
  have hInt : Integrable (fun w => |X w - Y w|) P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hX.sub hY).norm
  have hz : (∫ w, |X w - Y w| ∂P) = 0 :=
    le_antisymm hbound (integral_nonneg fun _ => abs_nonneg _)
  have ha := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun w => abs_nonneg (X w - Y w)) hInt).mp hz
  filter_upwards [ha] with w hw
  simpa only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] using hw
