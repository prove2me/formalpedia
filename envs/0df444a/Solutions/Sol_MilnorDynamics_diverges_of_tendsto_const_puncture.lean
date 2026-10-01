-- Prove2me | solution 1 for MilnorDynamics.diverges_of_tendsto_const_puncture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T22:22:42.842174+00:00
-- url     : https://prove2.me/submissions/08023e57-7ab0-4b6d-8db4-12d180721969

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Variant 1: separate the compact target from the puncture by a positive
`delta` obtained from the extreme value theorem, then use the compact-wise
characterisation of local uniform convergence. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → ℂ) (c : ℂ)
    (hcov : TendstoLocallyUniformlyOn f (fun _ => c) atTop U)
    (hc : c ∉ ({0, 1}ᶜ : Set ℂ)) :
    DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by
  intro K _hKU hK K' hK'V hK'
  have hδ : ∃ δ > 0, ∀ y ∈ K', δ ≤ dist c y := by
    by_cases hne : K'.Nonempty
    · obtain ⟨y0, hy0, hmin⟩ :=
        hK'.exists_isMinOn hne (continuous_const.dist continuous_id).continuousOn
      exact ⟨dist c y0, dist_pos.mpr (fun h => hc (h ▸ hK'V hy0)), fun y hy => hmin hy⟩
    · exact ⟨1, one_pos, fun y hy => absurd ⟨y, hy⟩ hne⟩
  obtain ⟨δ, hδpos, hδ⟩ := hδ
  have hev : ∀ᶠ n in atTop, ∀ x ∈ K, dist c (f n x) < δ :=
    (Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hcov K _hKU hK)) δ hδpos
  filter_upwards [hev] with n hn
  intro x hx hmem
  exact absurd (hn x hx) (not_lt.mpr (hδ (f n x) hmem))
