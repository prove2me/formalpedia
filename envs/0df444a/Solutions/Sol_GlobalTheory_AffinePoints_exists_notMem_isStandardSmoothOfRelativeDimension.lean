-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_notMem_isStandardSmoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:36.163822+00:00
-- url     : https://prove2.me/submissions/fa1db6c8-0905-40ac-92a8-58c1a92f211b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_trdeg_eq_of_etale

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
theorem _root_.solution [IsDomain A] [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) (P : Ideal A) [P.IsPrime] [Algebra.IsSmoothAt K P] :
    ∃ s ∉ P, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  obtain ⟨s, hs, ι, σ, _, _, ⟨Q⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K P
  refine ⟨s, hs, ?_⟩
  have hs0 : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors fun h => hs (h ▸ P.zero_mem)
  haveI : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization hs0
  haveI H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension K (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.dimension K (Localization.Away s)
  have h1 := trdeg_eq_of_etale g hg
  haveI : FaithfulSMul A (Localization.Away s) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)
  haveI : Algebra.IsAlgebraic A (Localization.Away s) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers s)
  rw [trdeg_eq_of_isAlgebraic_top K A (Localization.Away s)] at h1
  have h2 := ringKrullDim_eq_of_trdeg_eq K A h1
  rw [hd] at h2
  obtain rfl : d = Q.dimension := by exact_mod_cast h2
  exact H
end GlobalTheory.AffinePoints
