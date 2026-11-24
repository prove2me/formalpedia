-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RingDiag.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:30:50.830003+00:00
-- url     : https://prove2.me/submissions/00d37494-300d-44bb-990e-db660f57555e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinatePolynomialsFormMemKernelDifferential
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RingDiag
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {m : ℕ}
namespace GlobalTheory.CompanionTheory.SW.RingDiag
theorem _root_.solution (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (x : Fin n → A) (b : A)
    (hb : b * hform σ J x x = 1) : ∃ c : Fin n → A, ∑ i, c i * x i = 1 := by
  refine ⟨fun j => b * ∑ i, σ (x i) * J i j, ?_⟩
  rw [← hb, hform, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (b * ∑ i : Fin n, σ (x i) * J i j) * x j = b * ∑ i : Fin n, σ (x i) * J i j * x j
  rw [mul_assoc, Finset.sum_mul]
end GlobalTheory.CompanionTheory.SW.RingDiag
