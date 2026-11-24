-- Prove2me | solution 1 for GlobalTheory.NormSign.continuous_snorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:41.514335+00:00
-- url     : https://prove2.me/submissions/a7841dc9-9f50-4e81-8edb-691a095ce6ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.NormSign
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.NormSign
theorem _root_.solution : Continuous (snorm : mixedSpace K → ℝ) := by
  unfold snorm
  fun_prop
end GlobalTheory.NormSign
