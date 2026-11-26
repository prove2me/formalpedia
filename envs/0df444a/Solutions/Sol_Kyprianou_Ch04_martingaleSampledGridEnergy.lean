-- Prove2me | solution 1 for Kyprianou.Ch04.martingaleSampledGridEnergy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:04:35.898669+00:00
-- url     : https://prove2.me/submissions/18b72805-1d56-4e8a-8168-7095650f42f9

import Mathlib
import Theorems.Thm_Martingale_integral_sq_sum_eq_sum_integral_sq
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Orthogonality of martingale differences sampled on an arbitrary increasing grid. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (e : ℕ → NNReal) (he : Monotone e) (B : ℝ)
    (hV : ∀ j : ℕ, ∀ᵐ w ∂P, |M (e (j+1)) w-M (e j) w| ≤ B)
    (N : ℕ) :
    (∫ w, (M (e N) w-M (e 0) w)^2 ∂P) =
    ∑ j ∈ Finset.range N, ∫ w, (M (e (j+1)) w-M (e j) w)^2 ∂P := by
  let G : Filtration ℕ (inferInstance : MeasurableSpace Omega) :=
    { seq := fun j => F (e j)
      mono' := fun _ _ hij => F.mono (he hij)
      le' := fun j => F.le (e j) }
  let V : ℕ → Omega → ℝ := fun j w => M (e (j+1)) w-M (e j) w
  have hA (j : ℕ) : StronglyMeasurable[G (j+1)] (V j) :=
    (hM.stronglyAdapted _).sub ((hM.stronglyAdapted _).mono (F.mono (he (Nat.le_succ j))))
  have hMem (j : ℕ) : MemLp (V j) 2 P :=
    MemLp.of_bound ((hA j).mono (G.le (j+1))).aestronglyMeasurable _ (by
      simpa only [Real.norm_eq_abs,V] using hV j)
  have hmds (j : ℕ) : P[V j | G j] =ᵐ[P] 0 := by
    have ha := condExp_sub (hM.integrable (e (j+1))) (hM.integrable (e j)) (F (e j))
    have hb := hM.condExp_ae_eq (he (Nat.le_succ j))
    have hc := condExp_of_stronglyMeasurable (F.le (e j)) (hM.stronglyAdapted (e j))
      (hM.integrable (e j))
    filter_upwards [ha,hb] with w hw hwb
    change P[M (e (j+1)) - M (e j) | F (e j)] w = 0
    rw [hw,hc]
    exact sub_eq_zero.mpr hwb
  have hE := Martingale.integral_sq_sum_eq_sum_integral_sq P G V hMem hA hmds N
  have hs (w : Omega) : (∑ j ∈ Finset.range N, V j w) = M (e N) w-M (e 0) w :=
    Finset.sum_range_sub (fun j => M (e j) w) N
  rw [show (fun w => (∑ j ∈ Finset.range N, V j w)^2) =
      (fun w => (M (e N) w-M (e 0) w)^2) from funext fun w => congrArg (fun x : ℝ => x^2) (hs w)] at hE
  exact hE
