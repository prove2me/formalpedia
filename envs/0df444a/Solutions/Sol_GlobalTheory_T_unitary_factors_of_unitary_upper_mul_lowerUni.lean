-- Prove2me | solution 1 for GlobalTheory.T.unitary_factors_of_unitary_upper_mul_lowerUni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:01.436956+00:00
-- url     : https://prove2.me/submissions/ec0ff224-b1a2-447e-be46-4e6de713e475

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLowerStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_st_mul_self_of_factor


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
theorem _root_.solution : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ) (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ (rev : ι → ι), (∀ i, rev (rev i) = i) → (∀ i j, wt i < wt j → wt (rev j) < wt (rev i)) → Function.Injective wt → ∀ (st : E → E), (∀ a b, st (a * b) = st b * st a) → st 1 = 1 → st 0 = 0 → (∀ i, st (P i) = P (rev i)) → (∀ a a' : E, a * a' = 1 → a' * a = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a') → (∀ b b' : E, b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b → GlobalTheory.CompanionTheory.Iwahori.IsLower wt P b') → ∀ a a' b b' : E, a * a' = 1 → a' * a = 1 → b * b' = 1 → b' * b = 1 → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b → st (a * b) * (a * b) = 1 → (a * b) * st (a * b) = 1 → st a * a = 1 ∧ st b * b = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor | exact GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor | (intros; apply GlobalTheory.CompanionTheory.Iwahori.Unitary.st_mul_self_of_factor <;> assumption)
end _root_.GlobalTheory.T
