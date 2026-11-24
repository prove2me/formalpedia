-- Prove2me | solution 1 for GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:27.762577+00:00
-- url     : https://prove2.me/submissions/baef82c4-4150-4720-b635-3711dae44077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneReOpenNearOfIsUnit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneReOpenNearOfIsUnitStatement
import Theorems.Thm_GlobalTheory_traceOpen_near_of_isUnit


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.traceOpen_near_of_isUnit | exact GlobalTheory.traceOpen_near_of_isUnit | (intros; apply GlobalTheory.traceOpen_near_of_isUnit <;> assumption)
end _root_.GlobalTheory.T
