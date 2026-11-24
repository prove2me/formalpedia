-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.t2_tensor_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:36:13.882888+00:00
-- url     : https://prove2.me/submissions/ad1e8704-5793-4ca2-829c-de54d7dc803f

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
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hc : Continuous b.equivFun.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap _
  exact T2Space.of_injective_continuous b.equivFun.injective hc
end GlobalTheory.CompanionTheory.SW.StabFirst
