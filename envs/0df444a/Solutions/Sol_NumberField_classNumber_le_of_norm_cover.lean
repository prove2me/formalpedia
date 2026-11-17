-- Prove2me | solution 1 for NumberField.classNumber_le_of_norm_cover
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:57.865009+00:00
-- url     : https://prove2.me/submissions/0131d982-d273-4e6e-a506-1ba7ccafafb9

import Mathlib

set_option autoImplicit false

open scoped nonZeroDivisors

namespace NumberField

/-- Minkowski's theorem bounds the class number by any finite collection
containing every nonzero integral ideal within the Minkowski bound. -/
theorem _root_.solution
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))⁰)
    (hcover : ∀ I : (Ideal (𝓞 K))⁰,
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K).factorial /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
              Real.sqrt |(discr K : ℝ)|) → I ∈ s) :
    classNumber K ≤ s.card := by
  classical
  have hs : Function.Surjective
      (fun I : ↥s => ClassGroup.mk0 (I : (Ideal (𝓞 K))⁰)) := by
    intro C
    obtain ⟨I, hI, hnorm⟩ := exists_ideal_in_class_of_norm_le C
    exact ⟨⟨I, hcover I hnorm⟩, hI⟩
  simpa [classNumber] using Fintype.card_le_of_surjective _ hs

end NumberField
