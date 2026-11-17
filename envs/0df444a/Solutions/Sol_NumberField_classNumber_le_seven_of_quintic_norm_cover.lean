-- Prove2me | solution 1 for NumberField.classNumber_le_seven_of_quintic_norm_cover
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:58.466667+00:00
-- url     : https://prove2.me/submissions/afbc1a87-1375-4ae7-912c-78f56b1e5bf2

import Mathlib
import Theorems.Thm_NumberField_classNumber_le_of_norm_cover

set_option autoImplicit false

open scoped nonZeroDivisors

namespace NumberField

/-- The numerical Minkowski step for a totally real quintic field of
discriminant at most `5^8`. The finite ideal cover is a separate input. -/
theorem _root_.solution
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 5)
    (hcomplex : InfinitePlace.nrComplexPlaces K = 0)
    (hdiscr : |(discr K : ℝ)| ≤ 5 ^ 8)
    (s : Finset (Ideal (𝓞 K))⁰) (hcard : s.card ≤ 7)
    (hcover : ∀ I : (Ideal (𝓞 K))⁰,
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 24 → I ∈ s) :
    classNumber K ≤ 7 := by
  apply le_trans (classNumber_le_of_norm_cover K s ?_) hcard
  intro I hI
  apply hcover I
  have hsqrt : Real.sqrt |(discr K : ℝ)| ≤ 625 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · norm_num at hdiscr ⊢
      exact hdiscr
  rw [hdegree, hcomplex] at hI
  norm_num at hI
  have hnorm : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ 24 := by
    linarith
  exact_mod_cast hnorm

end NumberField
