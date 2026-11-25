-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:25:34.356483+00:00
-- url     : https://prove2.me/submissions/da6985df-6dfa-4903-b322-8679c34f31a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_exists_notMem_isStandardSmoothOfRelativeDimension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution [PerfectField K] [IsDomain A]
    [Algebra.FiniteType K A] (hd : ringKrullDim A = d) :
    ∃ s : A, s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.IsSmoothAt K (⊥ : Ideal A) := by
    haveI : IsLocalization (⊥ : Ideal A).primeCompl (FractionRing A) := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e := (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl (FractionRing A)
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars K
    haveI : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
    haveI : Algebra.FormallySmooth K (FractionRing A) := Algebra.FormallySmooth.of_perfectField
    exact Algebra.FormallySmooth.of_equiv e
  simpa using exists_notMem_isStandardSmoothOfRelativeDimension (K := K) hd ⊥
end GlobalTheory.AffinePoints
