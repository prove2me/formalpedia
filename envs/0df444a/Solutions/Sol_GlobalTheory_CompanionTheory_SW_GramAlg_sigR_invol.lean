-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.sigR_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:18.479484+00:00
-- url     : https://prove2.me/submissions/3b0281fe-94c8-48c1-84f2-20411432c7c4

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add, ha, hb]
end GlobalTheory.CompanionTheory.SW.GramAlg
