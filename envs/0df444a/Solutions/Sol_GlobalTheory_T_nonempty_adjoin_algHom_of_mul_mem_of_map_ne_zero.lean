-- Prove2me | solution 1 for GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:51.799217+00:00
-- url     : https://prove2.me/submissions/c3577966-653b-4a87-9c6c-a0a311c5f98f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominatorStatement
import Theorems.Thm_GlobalTheory_adjoin_hom_extend_of_denominator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S), ψ h ≠ 0 → ∀ T : Set F, (∀ x ∈ T, (h : F) * x ∈ S) → Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first | exact @GlobalTheory.adjoin_hom_extend_of_denominator | exact GlobalTheory.adjoin_hom_extend_of_denominator | (intros; apply GlobalTheory.adjoin_hom_extend_of_denominator <;> assumption)
end _root_.GlobalTheory.T
