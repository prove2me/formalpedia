-- Prove2me | solution 1 for NoHair.complete_static_double_from_reflection_and_point_chart
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:32:22.264655+00:00
-- url     : https://prove2.me/submissions/9b568b86-335c-4314-b63e-4af08ffaa6a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_reflected_static_double_metric_completion_one_point
import Theorems.Thm_NoHair_smooth_static_point_chart_is_topological_chart_of_completion
import Theorems.Thm_NoHair_compact_complement_surviving_end_of_completed_static_double
import Theorems.Thm_NoHair_smooth_riemannian_structure_on_static_metric_filling
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hcompact : ∀ R : ℝ, IsCompact ((d.inc true '' {x : ↥(closure Ω) | R < ‖x.val‖}) ∪ (d.inc false '' {x : ↥(closure Ω) | R < ‖x.val‖}))ᶜ)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    Nonempty (StaticConformalCompletion Ω N h) := by
  obtain ⟨p,np,_,exh⟩ := reflected_static_double_metric_completion_one_point Ω W N h c d hpositiveEnd hmass
  obtain ⟨p',e,off,es,atOrigin,agree⟩ := smooth_static_point_chart_is_topological_chart_of_completion Ω W N h c d a hpositiveEnd hmass
  have eq : p'=p := (exh p').resolve_right (fun ⟨q,hq⟩ => off q hq)
  obtain ⟨D,_,_⟩ := smooth_riemannian_structure_on_static_metric_filling Ω W N h c d a hpositiveEnd hmass
    p np exh e es (atOrigin.trans eq) agree (compact_complement_surviving_end_of_completed_static_double Ω W N h c d hpositiveEnd hmass)
  exact ⟨D⟩
