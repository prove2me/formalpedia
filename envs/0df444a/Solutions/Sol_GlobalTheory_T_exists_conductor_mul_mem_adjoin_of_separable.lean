-- Prove2me | solution 1 for GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:50.802619+00:00
-- url     : https://prove2.me/submissions/b6fb3f0c-10c4-47b0-8dde-a4f29ea8dfaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparableStatement
import Theorems.Thm_GlobalTheory_UnitLemma_exists_conductor_mul_mem_adjoin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g → ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u → algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  first | exact @GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | exact GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | (intros; apply GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin <;> assumption)
end _root_.GlobalTheory.T
