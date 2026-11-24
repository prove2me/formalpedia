-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.mat_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:40.533657+00:00
-- url     : https://prove2.me/submissions/be2f5bf9-29ea-4ec9-a0b8-2003a60dd795

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (P Q : Matrix n n R)
    (h : ∀ u v : n → R, u ⬝ᵥ (P *ᵥ v) = u ⬝ᵥ (Q *ᵥ v)) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)
end GlobalTheory.CompanionTheory.SW.TraceCoord
