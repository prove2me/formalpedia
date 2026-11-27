-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PRMNoOriginVersionV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:22:51.772065+00:00
-- url     : https://prove2.me/submissions/5468588d-ba55-4323-909d-ca0472a35e57

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_exercise45PRMIndistinguishableV2
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Choose an indistinguishable PRM with no atom at time zero on any path. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (h0 : ∀ᵐ w ∂P, N.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) :
    ∃ N' : PoissonRandomMeasure.{0,0,0} P ν,
      (∀ᵐ w ∂P, N'.N w = N.N w) ∧
      (∀ w, N'.N w (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0) := by
  let A : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ (univ : Set ℝ)
  let G : Set Ω := {w | N.N w A = 0}
  have hm : MeasurableSet G := measurableSet_eq_fun
    (N.measurable_eval (measurableSet_singleton 0 |>.prod MeasurableSet.univ))
    measurable_const
  let Q : Ω → Measure (ℝ × ℝ) := G.piecewise N.N (fun _ => 0)
  have hQ (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) : Measurable (fun w => Q w B) := by
    have he : (fun w => Q w B) = G.piecewise (fun w => N.N w B) (fun _ => 0) := by
      funext w
      by_cases hw : w ∈ G <;> simp [Q,Set.piecewise,hw]
    rw [he]
    exact (N.measurable_eval hB).piecewise hm measurable_const
  have he : ∀ᵐ w ∂P, N.N w = Q w := h0.mono fun w hw => by
    have hg : w ∈ G := hw
    simp [Q,Set.piecewise, hg]
  obtain ⟨N',hN'⟩ := Kyprianou.Ch04.exercise45PRMIndistinguishableV2 P ν N Q hQ he
  refine ⟨N',hN' ▸ (he.mono fun w hw => hw.symm),?_⟩
  intro w
  rw [hN']
  by_cases hw : w ∈ G
  · simpa [Q,Set.piecewise,hw] using (show N.N w A = 0 from hw)
  · simp [Q,Set.piecewise,hw]
