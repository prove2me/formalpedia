-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.rmul_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:51.454662+00:00
-- url     : https://prove2.me/submissions/d630e5e6-0d0d-4c70-94b2-3c3af74c14cf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
omit [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (A B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : rmul R (rmul R X A) B = rmul R X (A * B) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.SW.LatRat
