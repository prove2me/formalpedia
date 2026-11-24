-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLevyMarginalForcesZeroGaussianV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:20:37.264344+00:00
-- url     : https://prove2.me/submissions/22902f03-9d4f-4774-8c61-fab71e7c089e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_pureJumpMarginalExplicitLawV1
import Theorems.Thm_Kyprianou_Ch02_nondegenerateGaussianConvolutionNegativeMassV1
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Iio (0 : ℝ)) = 0)
    (hchar : ∀ ξ : ℝ, charFun Q ξ = Complex.exp (Kyprianou.Ch01.levyTripleExponent T ξ)) :
    T.gaussianVariance = 0 := by
  by_contra hne
  obtain ⟨R, hRp, hR⟩ := Kyprianou.Ch02.pureJumpMarginalExplicitLawV1 T
  letI : IsProbabilityMeasure R := hRp
  have he : Q = R ∗ gaussianReal 0 T.gaussianVariance := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [hchar ξ, charFun_conv, hR ξ, charFun_gaussianReal, ← Complex.exp_add]
    congr 1
    unfold Kyprianou.Ch01.levyTripleExponent
    push_cast
    ring
  have hp := Kyprianou.Ch02.nondegenerateGaussianConvolutionNegativeMassV1 R
    T.gaussianVariance (pos_iff_ne_zero.mpr hne)
  rw [← he, hQ] at hp
  exact lt_irrefl 0 hp
