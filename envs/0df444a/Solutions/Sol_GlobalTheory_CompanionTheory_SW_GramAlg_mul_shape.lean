-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.mul_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:16.964413+00:00
-- url     : https://prove2.me/submissions/c1da87f1-2176-4ce6-9c15-d3396a6f31b6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {A : Type} [CommRing A] {M n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution {p q r s t u : Type} [Fintype q] [Fintype r] [Fintype s] [Fintype t]
    (a : Matrix p q A) (b : Matrix q r A) (c : Matrix r s A) (d : Matrix s t A) (e : Matrix t u A) :
    (((a * b : Matrix p r A) * c : Matrix p s A) * (d * e : Matrix s u A) : Matrix p u A) =
      ((a * ((b * c : Matrix q s A) * d : Matrix q t A) : Matrix p t A) * e : Matrix p u A) := by
  simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.GramAlg
