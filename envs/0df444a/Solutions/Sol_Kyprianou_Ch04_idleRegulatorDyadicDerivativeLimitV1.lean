-- Prove2me | solution 1 for Kyprianou.Ch04.idleRegulatorDyadicDerivativeLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:17:25.886516+00:00
-- url     : https://prove2.me/submissions/f9d6b3e2-76fa-4947-a85d-3902e280d2e4

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (R : NNReal → Real) (t : Real) (ht0 : 0 ≤ t)
    (hdiff : DifferentiableAt Real (fun s : Real => R s.toNNReal) t) :
    let delta : Nat → NNReal := fun n => ((1 : NNReal) / 2) ^ n
    (∀ n, 0 < (delta n : Real)) ∧
    Tendsto (fun n => (delta n : Real)) atTop (𝓝 0) ∧
    Tendsto (fun n => (R (t.toNNReal + delta n) - R t.toNNReal) / (delta n : Real))
      atTop (𝓝 (deriv (fun s : Real => R s.toNNReal) t)) := by
  intro delta
  let Rr : Real → Real := fun s => R s.toNNReal
  let u := t.toNNReal
  let r : Nat → Real := fun n => (R (u + delta n) - R u) / (delta n : Real)
  have hpos (n : Nat) : 0 < (delta n : Real) := by dsimp [delta]; positivity
  have hstep : Tendsto (fun n => (delta n : Real)) atTop (𝓝 0) := by
    simpa [delta] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1:Real)/2)
        (by norm_num : (1:Real)/2 < 1))
  have hwithin : Tendsto (fun n => (delta n : Real)) atTop
      (𝓝[({0} : Set Real)ᶜ] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hstep, Eventually.of_forall (fun n => by
      simpa using (hpos n).ne')⟩
  have hlim : Tendsto r atTop (𝓝 (deriv Rr t)) := by
    have h := hdiff.hasDerivAt.tendsto_slope_zero.comp hwithin
    refine h.congr (fun n => ?_)
    dsimp [Function.comp_def, Rr, r, u]
    rw [Real.toNNReal_add ht0 (hpos n).le, Real.toNNReal_coe]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact ⟨hpos, hstep, hlim⟩
