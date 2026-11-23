-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockAlg.blockOne_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:42.872246+00:00
-- url     : https://prove2.me/submissions/c14814ef-86c4-45eb-9ce5-e308b4ac0c9a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
variable {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
namespace GlobalTheory.CompanionTheory.SW.BlockAlg
theorem _root_.solution (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl
end GlobalTheory.CompanionTheory.SW.BlockAlg
