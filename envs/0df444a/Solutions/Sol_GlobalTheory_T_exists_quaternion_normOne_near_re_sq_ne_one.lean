-- Prove2me | solution 1 for GlobalTheory.T.exists_quaternion_normOne_near_re_sq_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:01.138836+00:00
-- url     : https://prove2.me/submissions/63675ec9-7585-4964-bf7a-3016dd4c7486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsQuaternionNormOneNearReSqNeOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsQuaternionNormOneNearReSqNeOneStatement
import Theorems.Thm_GlobalTheory_QSA_exists_nrm_one_re_sq_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K], (2 : K) ≠ 0 → (𝓝[≠] (0 : K)).NeBot → ∀ a b : K, a ≠ 0 → ∀ g : ℍ[K, a, b], nrm g = 1 → ∀ W : Set ℍ[K, a, b], W ∈ 𝓝 g → ∃ g' : ℍ[K, a, b], nrm g' = 1 ∧ g'.re ^ 2 ≠ 1 ∧ W ∈ 𝓝 g' := by
  first | exact @GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one | exact GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one | (intros; apply GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one <;> assumption)
end _root_.GlobalTheory.T
