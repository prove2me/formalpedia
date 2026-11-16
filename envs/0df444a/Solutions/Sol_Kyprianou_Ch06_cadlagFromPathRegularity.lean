-- Prove2me | solution 1 for Kyprianou.Ch06.cadlagFromPathRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:04:09.803657+00:00
-- url     : https://prove2.me/submissions/f6919e48-0deb-408f-9207-520c207b0bbc

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal

/-- Transfer Chapter 6 path regularity to the published cadlag predicate,
including the vacuous left limit at the minimal time zero. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hregular : ∀ᵐ ω ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u : NNReal => X u ω) (Set.Ici t) t ∧
      (t = 0 ∨ ∃ x : Real,
        Tendsto (fun u : NNReal => X u ω)
          (nhdsWithin t (Set.Iio t)) (nhds x))) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag (fun t : NNReal => X t ω) := by
  filter_upwards [hregular] with ω hω
  intro t
  rcases hω t with ⟨hright, hleft⟩
  refine ⟨hright, ?_⟩
  rcases hleft with ht | hlim
  · subst t
    refine ⟨X 0 ω, ?_⟩
    have hempty : (Set.Iio (0 : NNReal)) = ∅ := by
      ext u
      simp
    simp [hempty]
  · exact hlim
