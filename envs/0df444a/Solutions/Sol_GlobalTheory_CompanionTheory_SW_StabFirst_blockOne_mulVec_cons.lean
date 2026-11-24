-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.blockOne_mulVec_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:36:10.944117+00:00
-- url     : https://prove2.me/submissions/10e9a2b6-16a5-46e9-bb7f-76dad6d95524

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
theorem _root_.solution (A : Matrix (Fin M) (Fin M) K) (x : Fin M → K) :
    (blockOne 1 A).mulVec (Fin.cons 0 x) = Fin.cons 0 (A.mulVec x) := by
  ext a
  refine Fin.cases ?_ (fun i => ?_) a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
end GlobalTheory.CompanionTheory.SW.StabFirst
