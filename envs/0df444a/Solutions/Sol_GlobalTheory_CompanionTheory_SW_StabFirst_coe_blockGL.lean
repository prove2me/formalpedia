-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.coe_blockGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:05.505425+00:00
-- url     : https://prove2.me/submissions/6d682b67-3157-44ff-8547-79d918a51303

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
variable {K : Type} [CommRing K] {M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution (g : GL (Fin M) K) :
    ((blockGL g : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) =
      blockOne 1 (g : Matrix (Fin M) (Fin M) K) := rfl
end GlobalTheory.CompanionTheory.SW.StabFirst
