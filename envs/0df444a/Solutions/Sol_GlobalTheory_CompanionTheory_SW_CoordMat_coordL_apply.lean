-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CoordMat.coordL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:19.016549+00:00
-- url     : https://prove2.me/submissions/040a342e-d975-4974-84bf-b3c9e6aeca21

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.CoordMat
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (M : ℕ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (x : Fin M → R ⊗[F] E) (p : Fin M × Fin d) :
    coordL R M b x p = (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := rfl
end GlobalTheory.CompanionTheory.SW.CoordMat
