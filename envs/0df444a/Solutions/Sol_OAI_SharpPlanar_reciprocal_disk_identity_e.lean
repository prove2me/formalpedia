-- Prove2me | solution 1 for OAI.SharpPlanar.reciprocal_disk_identity_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:12:01.050949+00:00
-- url     : https://prove2.me/submissions/9e3b9cc1-1c8c-4174-bec0-813cc742b5ad

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex


lemma reciprocal_disk_identity_e_oai (a ζ : ℂ) (r : ℝ)
    (hΔ : Complex.normSq a-r^2 ≠ 0) :
    Complex.normSq (1-a*ζ)-r^2*Complex.normSq ζ =
      (Complex.normSq a-r^2)*Complex.normSq
        (ζ-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a) -
          r^2/(Complex.normSq a-r^2) := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,
    Complex.mul_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,zero_mul] at *
  simp only [← sq] at hΔ
  field_simp [hΔ]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.reciprocal_disk_identity_e_oai := @OAI.SharpPlanar.reciprocal_disk_identity_e_oai
