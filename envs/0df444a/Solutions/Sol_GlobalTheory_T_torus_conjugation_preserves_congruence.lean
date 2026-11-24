-- Prove2me | solution 1 for GlobalTheory.T.torus_conjugation_preserves_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:26.580641+00:00
-- url     : https://prove2.me/submissions/b3eeffcb-6537-47f3-80d2-94593f23c78f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruence
import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusConjugationPreservesCongruenceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_TorusConj_conj_congruence


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {L E ι : Type} [NormedField L] [Ring E] [Algebra L E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E, GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → (∀ c : L, ‖c‖ ≤ 1 → ∀ x ∈ J, c • x ∈ J) → ∀ (T T' : E) (τ : ι → L), (∀ i, τ i ≠ 0) → T * T' = 1 → T' * T = 1 → (∀ i, T * P i = τ i • P i) → (∀ i, P i * T = τ i • P i) → (∀ i j, wt i ≤ wt j → ‖τ i‖ ≤ ‖τ j‖) → ∀ a b : E, a - 1 ∈ J → b - 1 ∈ J → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → T * a * T' - 1 ∈ J ∧ T' * b * T - 1 ∈ J := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | exact GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence | (intros; apply GlobalTheory.CompanionTheory.Iwahori.TorusConj.conj_congruence <;> assumption)
end _root_.GlobalTheory.T
