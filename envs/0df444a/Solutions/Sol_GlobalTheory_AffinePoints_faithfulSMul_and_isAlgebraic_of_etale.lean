-- Prove2me | solution 1 for GlobalTheory.AffinePoints.faithfulSMul_and_isAlgebraic_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:03.288876+00:00
-- url     : https://prove2.me/submissions/129fae2a-26ef-4de6-b688-c4a894bd9cfb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension

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
theorem _root_.solution (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    FaithfulSMul R S ∧ Algebra.IsAlgebraic R S := by
  haveI : FaithfulSMul R S := inferInstance
  exact ⟨this, isAlgebraic_of_quasiFiniteAt R S ⊥⟩
end GlobalTheory.AffinePoints
