-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorDerivativeFromDyadicV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:26:04.227418+00:00
-- url     : https://prove2.me/submissions/5ed56faf-20b3-4953-8339-2e69c8447f8a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorNumericalSlopeV1
import Theorems.Thm_Kyprianou_Ch04_idleRegulatorDyadicDerivativeLimitV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f R : NNReal → Real) (d : Real) (hd : 0 < d)
    (hdom : ∀ t, f t ≤ R t)
    (hinc : ∀ s t : NNReal, s ≤ t →
      0 ≤ R t - R s ∧
      R t - R s ≤ max 0 (f s - R s + d * ((t : Real) - (s : Real))))
    (hLip : LipschitzWith (Real.toNNReal d) R)
    (hSlope : ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      Tendsto (fun n : Nat =>
        (d * ((((1 : NNReal) / 2) ^ n : NNReal) : Real) -
          (f (Real.toNNReal t + ((1 : NNReal) / 2) ^ n) -
            f (Real.toNNReal t))) /
          ((((1 : NNReal) / 2) ^ n : NNReal) : Real))
        atTop (𝓝 (0 : Real))) :
    ∀ᵐ t : Real ∂(volume.restrict (Ici 0)),
      deriv (fun s : Real => R (Real.toNNReal s)) t =
        if R (Real.toNNReal t) - f (Real.toNNReal t) = 0 then d else 0 := by
  let Rr : Real → Real := fun t => R t.toNNReal
  have hL : LipschitzWith d.toNNReal Rr := by
    simpa [Rr, Function.comp_def] using hLip.comp Real.lipschitzWith_toNNReal
  filter_upwards [hSlope, ae_restrict_of_ae hL.ae_differentiableAt_real,
    ae_restrict_mem measurableSet_Ici] with t ht hdiff ht0
  let delta : Nat → NNReal := fun n => ((1 : NNReal) / 2) ^ n
  let u := t.toNNReal
  let r : Nat → Real := fun n => (R (u + delta n) - R u) / (delta n : Real)
  let q : Nat → Real := fun n => (d * (delta n : Real) -
    (f (u + delta n) - f u)) / (delta n : Real)
  obtain ⟨hpos, hstep, hlim⟩ :=
    Kyprianou.Ch04.idleRegulatorDyadicDerivativeLimitV1 R t ht0 hdiff
  have hq : Tendsto q atTop (𝓝 0) := ht
  have hB (n : Nat) := hinc u (u + delta n) (by simp)
  have hB' (n : Nat) : 0 ≤ R (u + delta n) - R u ∧
      R (u + delta n) - R u ≤ max 0 (f u - R u + d * (delta n : Real)) := by
    simpa [NNReal.coe_add, add_sub_cancel_left] using hB n
  change deriv Rr t = if R u - f u = 0 then d else 0
  apply Kyprianou.Ch04.idleRegulatorNumericalSlopeV1 d (R u - f u)
    (deriv Rr t) hd (sub_nonneg.mpr (hdom u)) (fun n => (delta n : Real)) r q
    hpos hstep hq hlim
  · intro n
    refine ⟨div_nonneg (hB' n).1 (hpos n).le, ?_⟩
    apply (div_le_div_iff_of_pos_right (hpos n)).mpr
    rw [show -(R u - f u) = f u - R u by ring]
    exact (hB' n).2
  · intro hc n
    have hEq : R u = f u := sub_eq_zero.mp hc
    dsimp [q, r]
    have he : d - (d * (delta n : Real) - (f (u + delta n) - f u)) /
        (delta n : Real) = (f (u + delta n) - f u) / (delta n : Real) := by
      have hn : (delta n : Real) ≠ 0 := (hpos n).ne'
      rw [sub_div, mul_div_cancel_right₀ _ hn]
      ring
    rw [he]
    apply (div_le_div_iff_of_pos_right (hpos n)).mpr
    linarith [hdom (u + delta n)]
