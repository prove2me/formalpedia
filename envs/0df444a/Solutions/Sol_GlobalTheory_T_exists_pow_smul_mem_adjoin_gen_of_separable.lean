-- Prove2me | solution 1 for GlobalTheory.T.exists_pow_smul_mem_adjoin_gen_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:22.796977+00:00
-- url     : https://prove2.me/submissions/1fdff99d-cf12-4d30-8a46-6daf4d4ffa00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSmulMemAdjoinGenStatement
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_pow_smul_mem_adjoin_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (a : K.O), B.P.Separable → K.Small a → ∃ N : ℕ, ∀ r : B.A, IsIntegral K.O r → (al K a ^ N) • r ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | exact GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen | (intros; apply GlobalTheory.UnitLemma.Desc.pow_smul_mem_adjoin_gen <;> assumption)
end _root_.GlobalTheory.T
