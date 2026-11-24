-- Prove2me | solution 1 for GlobalTheory.AffinePoints.dense_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:09.506243+00:00
-- url     : https://prove2.me/submissions/1ec06e68-fcb0-41d9-89b1-66b2c6c95e11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AffinePoints_volume_coords_image_zeroSet
import Theorems.Thm_GlobalTheory_AffinePoints_dense_compl_of_volume_coords_image

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
theorem _root_.solution [IsDomain A] [Algebra.FiniteType ℂ A] {f : A} (hf : f ≠ 0) :
    Dense {p : A →ₐ[ℂ] ℂ | p f ≠ 0} := by
  obtain ⟨s, g, hinj, hg⟩ := exists_finite_inj_algHom_of_fg ℂ A
  refine dense_compl_of_volume_coords_image g hg hinj (volume_coords_image_zeroSet g ?_ hf)
  letI := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) ℂ) A := hg
  infer_instance
end GlobalTheory.AffinePoints
