-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.finite_zeros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:11:28.7063+00:00
-- url     : https://prove2.me/submissions/815d5a95-9c41-41f2-9d2c-5c9da5c6ae53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
import Theorems.Thm_GlobalTheory_ExplicitRect_exists_entire

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite := by
  obtain ⟨F, hF, hF1, hFz⟩ := exists_entire χ
  have hZc : IsCompact ({ρ : ℂ | F ρ = 0} ∩ Metric.closedBall 0 (1 + T)) :=
    (isCompact_closedBall 0 (1 + T)).inter_left (isClosed_eq hF.continuous continuous_const)
  have hFa : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  rcases hFa.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact absurd (h (Set.mem_univ 1)) hF1
  have hd : IsDiscrete ({ρ : ℂ | F ρ = 0} ∩ Metric.closedBall 0 (1 + T)) := by
    rw [isDiscrete_iff_nhdsNE]
    intro x _
    rw [Filter.eventually_iff, mem_codiscreteWithin] at h
    have hx := h x (Set.mem_univ _)
    rw [disjoint_iff] at hx
    have hsub : {ρ : ℂ | F ρ = 0} ∩ Metric.closedBall 0 (1 + T) ⊆ Set.univ \ {x | F x ≠ 0} :=
      fun y hy => ⟨Set.mem_univ _, fun h' => h' hy.1⟩
    exact le_bot_iff.mp ((inf_le_inf_left _ (Filter.principal_mono.mpr hsub)).trans hx.le)
  refine (hZc.finite hd).subset fun ρ hρ => ?_
  obtain ⟨h0, h1, hT, hL⟩ := hρ
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp at h1
  refine ⟨hFz ρ hρ1 hL, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
  rw [abs_of_pos h0]
  linarith
end GlobalTheory.ExplicitRect
