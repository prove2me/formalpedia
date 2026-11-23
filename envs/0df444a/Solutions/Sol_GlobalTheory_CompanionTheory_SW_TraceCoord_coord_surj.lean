-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.coord_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:01.595868+00:00
-- url     : https://prove2.me/submissions/0336bc5a-544b-4d5a-a6df-09ba7e8fca9e

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
theorem _root_.solution (β : Module.Basis (Fin d) R A) (u : Fin M × Fin d → R) :
    ∃ x : Fin M → A, coord β x = u := by
  refine ⟨fun i => ∑ k, u (i, k) • β k, ?_⟩
  funext p
  change β.repr (∑ k, u (p.1, k) • β k) p.2 = u p
  rw [Module.Basis.repr_sum_self]
end GlobalTheory.CompanionTheory.SW.TraceCoord
