-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.isEmbedding_pairMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:06.012886+00:00
-- url     : https://prove2.me/submissions/2467b283-84fe-43b2-9a35-2d35517a217f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) :
    IsEmbedding (pairMap R σ J') :=
  (Units.isEmbedding_embedProduct).comp
    (IsEmbedding.subtypeVal (p := fun g => g ∈ HR R σ J'))
end GlobalTheory.CompanionTheory.SW.StabFirst
