-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.mulVec_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:52.816089+00:00
-- url     : https://prove2.me/submissions/e8343b7c-b89d-4ee1-93d5-68bd4227aa71

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
theorem _root_.solution (A : Matrix (Fin (M + 1)) (Fin (M + 1)) K) (a : Fin (M + 1)) :
    A.mulVec (Fin.cons 1 (fun _ => 0)) a = A a 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
end GlobalTheory.CompanionTheory.SW.StabFirst
