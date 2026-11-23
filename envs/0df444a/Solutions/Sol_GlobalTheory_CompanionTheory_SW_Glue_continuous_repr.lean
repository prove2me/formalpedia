-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Glue.continuous_repr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:56.689384+00:00
-- url     : https://prove2.me/submissions/1866249c-0af5-470f-9748-0564d096a64c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.SW.Glue
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) (k : Fin d) :
    Continuous fun y : R ⊗[F] E => (Algebra.TensorProduct.basis R b).repr y k :=
  (continuous_apply k).comp (coH R b).continuous
end GlobalTheory.CompanionTheory.SW.Glue
