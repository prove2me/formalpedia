-- Prove2me | solution 1 for GlobalTheory.AffinePoints.trdeg_eq_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:21.194801+00:00
-- url     : https://prove2.me/submissions/3eeeb302-acac-42fd-9b1c-be0c30f23c23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_faithfulSMul_and_isAlgebraic_of_etale

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
theorem _root_.solution [IsDomain A] (g : MvPolynomial (Fin d) K →ₐ[K] A) (hg : g.Etale) :
    Algebra.trdeg K A = d := by
  letI : Algebra (MvPolynomial (Fin d) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) A := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨_, _⟩ := faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin d) K) A
  rw [trdeg_eq_of_isAlgebraic_top K (MvPolynomial (Fin d) K) A, MvPolynomial.trdeg_of_isDomain]
  simp
end GlobalTheory.AffinePoints
