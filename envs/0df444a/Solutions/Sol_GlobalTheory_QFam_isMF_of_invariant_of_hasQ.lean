-- Prove2me | solution 1 for GlobalTheory.QFam.isMF_of_invariant_of_hasQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:58.293474+00:00
-- url     : https://prove2.me/submissions/2046e5e1-34af-43ba-a8e5-ab7f6662d97a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQMdifferentiableAndIsBoundedAtImInftyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsModularFormLevelOneOfInvariantQExpansion
import Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable
import Theorems.Thm_GlobalTheory_QFam_HasQ_mdifferentiable
import Theorems.Thm_GlobalTheory_QFam_hasQ_mdifferentiable_and_isBoundedAtImInfty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory GlobalTheory.QFam
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
namespace GlobalTheory.QFam
namespace _root_.GlobalTheory.QFam
theorem _root_.solution : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by
  intro N k f a hN hinv h
  refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ },
    fun _ => rfl⟩
  · rintro _ ⟨γ, rfl⟩
    exact (ModularForm.SL_slash f γ).symm.trans (hinv γ)
  · exact h.mdifferentiable hN
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hinv γ]
    exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN h).2
end _root_.GlobalTheory.QFam
end GlobalTheory.QFam
