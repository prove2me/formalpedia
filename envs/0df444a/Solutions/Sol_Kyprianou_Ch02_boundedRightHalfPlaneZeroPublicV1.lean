-- Prove2me | solution 1 for Kyprianou.Ch02.boundedRightHalfPlaneZeroPublicV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:48:33.029726+00:00
-- url     : https://prove2.me/submissions/2deee2c6-512d-439b-8c60-51813ae80b66

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

open Asymptotics Bornology
open scoped Asymptotics Filter Real
theorem solution (f : ℂ → ℂ)
    (hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (M : ℝ) (hb : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ M)
    (hzero : ∀ x : ℝ, f ((x : ℂ) * Complex.I) = 0)
    (z : ℂ) (hz : 0 ≤ z.re) : f z = 0 := by
  have ho : ∃ c < (2 : ℝ), ∃ B,
      f =O[cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
        fun w => Real.exp (B * ‖w‖ ^ c) := by
    refine ⟨0, by norm_num, 0, Asymptotics.isBigO_iff.mpr ⟨M, ?_⟩⟩
    apply Filter.eventually_inf_principal.mpr
    exact Filter.Eventually.of_forall fun w hw => by simpa using hb w hw.le
  have hr : IsBoundedUnder (· ≤ ·) atTop (fun x : ℝ => ‖f x‖) :=
    isBoundedUnder_of_eventually_le (eventually_atTop.2
      ⟨0, fun x hx => hb (x : ℂ) (by simpa using hx)⟩)
  have h := PhragmenLindelof.right_half_plane_of_bounded_on_real
    (C := 0) hd ho hr (fun x => by simp [hzero x]) hz
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

