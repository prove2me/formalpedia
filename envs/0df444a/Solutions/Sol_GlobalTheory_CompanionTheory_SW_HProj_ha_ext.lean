-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HProj.ha_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:38.449592+00:00
-- url     : https://prove2.me/submissions/e232a8f8-4e73-4ba4-b671-3ceba2bfdc78

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
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {g h : HA R σ J}
    (e : ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (HA.mat R σ J h : GL _ _)) :
    g = h :=
  Subtype.ext (Units.ext e)
end GlobalTheory.CompanionTheory.SW.HProj
