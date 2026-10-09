-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.expRevenue_one_shift_mono_nonpos_fare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T17:01:35.186325+00:00
-- url     : https://prove2.me/submissions/a35ecd55-3742-4305-8c52-17750109f835

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_integrable_of_seat_model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_scalar_min_shift_mono_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (hf1 : f 1 ≤ 0) :
    MonotoneOn
      (fun s => expRevenue P X f p 1 s - f 1 * s) (Set.Ici 0) := by
  letI : IsProbabilityMeasure P := hM.isProb
  let G : ℝ → Ω → ℝ := fun s ω => f 1 * min s (X 1 ω)
  have hpoint (s : ℝ) (ω : Ω) :
      revenue f p (fun i => X i ω) 1 s = G s ω := by
    change (if s < X 1 ω then f 1 * s else f 1 * X 1 ω) =
      f 1 * min s (X 1 ω)
    by_cases hs : s < X 1 ω
    · simp [hs, min_eq_left (le_of_lt hs)]
    · simp [hs, min_eq_right (le_of_not_gt hs)]
  have hInt (s : ℝ) (hs : 0 ≤ s) :
      Integrable (G s) P := by
    have hRev := revenue_integrable_of_seat_model
      P X f p hM hp 0 s hs
    have heq : G s =
      (fun ω => revenue f p (fun i => X i ω) 1 s) := by
      funext ω
      exact (hpoint s ω).symm
    rw [heq]
    exact hRev
  have hRep (s : ℝ) : expRevenue P X f p 1 s =
      ∫ ω, G s ω ∂P := by
    unfold expRevenue
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hpoint s)
  have hConst (s : ℝ) :
      Integrable (fun _ : Ω => f 1 * s) P :=
    integrable_const (f 1 * s)
  have hShift (s : ℝ) (hs : 0 ≤ s) :
      expRevenue P X f p 1 s - f 1 * s =
        ∫ ω, (G s ω - f 1 * s) ∂P := by
    rw [hRep s]
    rw [integral_sub (hInt s hs) (hConst s)]
    simp
  intro s hs t ht hst
  change expRevenue P X f p 1 s - f 1 * s ≤
    expRevenue P X f p 1 t - f 1 * t
  rw [hShift s hs, hShift t ht]
  have h1 : Integrable (fun ω => G s ω - f 1 * s) P :=
    (hInt s hs).sub (hConst s)
  have h2 : Integrable (fun ω => G t ω - f 1 * t) P :=
    (hInt t ht).sub (hConst t)
  apply integral_mono_ae h1 h2
  apply Filter.Eventually.of_forall
  intro ω
  exact scalar_min_shift_mono_nonpos (f 1) s t (X 1 ω) hf1 hst
