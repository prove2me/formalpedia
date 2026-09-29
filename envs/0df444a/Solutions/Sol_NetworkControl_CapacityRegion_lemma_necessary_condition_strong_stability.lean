-- Prove2me | solution 1 for NetworkControl.CapacityRegion.lemma_necessary_condition_strong_stability
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T14:23:01.085751+00:00
-- url     : https://prove2.me/submissions/ded6fb24-92e0-44b8-a05a-4d05adb59a9a

import Mathlib
import Definitions.Def_NetworkControl_CapacityRegion_StronglyStable

/-! Disproof of 3b5b4cb3 `NetworkControl.CapacityRegion.lemma_necessary_condition_strong_stability`.

The statement never links `U` to `A` or `svc`, and `StronglyStable` only bounds the Cesàro
averages of `U` from above. Take `U t = -t`, `A = svc = 0`, `Amax = Dmax = 0`. Every Cesàro
average is `≤ 0`, and `A t ≤ 0` holds, but `U t / t = -1` for `t ≥ 1`, so it tends to `-1 ≠ 0`. -/

set_option autoImplicit false

open NetworkControl.CapacityRegion in
theorem solution : ¬ (∀ (U A svc : ℕ → ℝ) (Amax Dmax : ℝ) (hAmax : 0 ≤ Amax) (hDmax : 0 ≤ Dmax)
    (hstable : StronglyStable U)
    (hbound : (∀ t : ℕ, A t ≤ Amax) ∨ (∀ t : ℕ, svc t - A t ≤ Dmax)),
    Filter.Tendsto (fun t : ℕ => U t / (t : ℝ)) Filter.atTop (nhds 0)) := by
  intro H
  have hst : StronglyStable (fun t : ℕ => -(t : ℝ)) := by
    refine ⟨0, fun t => ?_⟩
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · exact Finset.sum_nonpos (fun i _ => by simp)
  have key := H (fun t : ℕ => -(t : ℝ)) (fun _ => 0) (fun _ => 0) 0 0 le_rfl le_rfl hst
    (Or.inl fun _ => le_rfl)
  have hev : (fun t : ℕ => -(t : ℝ) / (t : ℝ)) =ᶠ[Filter.atTop] fun _ => (-1 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with t ht
    have : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    field_simp
  have h2 := (key.congr' hev)
  have h3 : (-1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h2
  norm_num at h3
