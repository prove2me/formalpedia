-- Prove2me | solution 1 for GlobalTheory.T.SL2_bruhat_decompositions_and_w_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:36.281333+00:00
-- url     : https://prove2.me/submissions/a0bd733f-9d7d-48ab-87da-4bfc9b7394d0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SL2BruhatDecompositionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SL2BruhatDecompositionIdentitiesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_SL2BruhatDecomposition_decompositions


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (g : SL(2, R)), (∀ c : Rˣ, g 1 0 = (c : R) → g = nMat (g 0 0 * ((c⁻¹ : Rˣ) : R)) * mMat (-c⁻¹) * wMat * nMat (g 1 1 * ((c⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g = wMat⁻¹ * nMat (-(g 1 0 * ((a⁻¹ : Rˣ) : R))) * wMat * mMat a * nMat (g 0 1 * ((a⁻¹ : Rˣ) : R))) ∧ (∀ a : Rˣ, g 0 0 = (a : R) → g 1 0 = 0 → g = nMat (g 0 1 * (a : R)) * mMat a) ∧ (wMat : SL(2, R))⁻¹ = wMat * wMat * wMat := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | exact GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions | (intros; apply GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions <;> assumption)
end _root_.GlobalTheory.T
