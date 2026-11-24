-- Prove2me | solution 1 for GlobalTheory.AffinePoints.dense_compl_of_volume_coords_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:16.210318+00:00
-- url     : https://prove2.me/submissions/8b32c8df-0c92-404b-931e-5ae53514ae2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_isOpenMap_coords

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
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
namespace GlobalTheory.AffinePoints
theorem _root_.solution [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : g.Finite) (hinj : Function.Injective g) {S : Set (A →ₐ[ℂ] ℂ)}
    (hS : volume (coords g '' S) = 0) : Dense Sᶜ := by
  have h1 : Dense (coords g '' S)ᶜ :=
    Measure.dense_of_ae (μ := volume) (measure_eq_zero_iff_ae_notMem.1 hS)
  refine (h1.preimage (isOpenMap_coords g hg hinj)).mono ?_
  intro p hp hpS
  exact hp ⟨p, hpS, rfl⟩
end GlobalTheory.AffinePoints
