-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.hMap_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:37.065824+00:00
-- url     : https://prove2.me/submissions/cc973a77-a2e6-4acd-9efb-515b89ec49ed

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F : Type} (E : Type) [Field F] [Field E] [Algebra F E]
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']
variable {E}
namespace GlobalTheory.CompanionTheory.SW.HProj
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] R')
    (h : HA R σ J) :
    ((HA.mat R' σ J (hMap σ J φ h) : GL _ _) : Matrix (Fin M) (Fin M) (R' ⊗[F] E)) =
      ((HA.mat R σ J h : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (tm E φ) := rfl
end GlobalTheory.CompanionTheory.SW.HProj
