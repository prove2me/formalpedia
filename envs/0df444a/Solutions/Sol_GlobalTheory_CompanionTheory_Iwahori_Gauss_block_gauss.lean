-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.block_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:23.5128+00:00
-- url     : https://prove2.me/submissions/f8118638-6a45-45d2-870c-b25a998e86c2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_exists_of_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Gauss
open GlobalTheory.CompanionTheory.Iwahori
variable {E ι : Type} [Ring E] [Fintype ι] {wt : ι → ℕ} {P : ι → E}
namespace GlobalTheory.CompanionTheory.Iwahori.Gauss
theorem _root_.solution : ∀ {E ι : Type} [Ring E] [Fintype ι] (wt : ι → ℕ), Function.Injective wt →
    ∀ (P : ι → E), GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ J : AddSubgroup E,
    GlobalTheory.CompanionTheory.Iwahori.IsCongIdeal J P → ∀ k : E, k - 1 ∈ J →
    ∃ a b : E, a - 1 ∈ J ∧ b - 1 ∈ J ∧ GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a ∧
      GlobalTheory.CompanionTheory.Iwahori.IsLowerUni wt P b ∧ k = a * b := by
  intro E ι _ _ wt hwt P hP J hJ k hk
  refine exists_of_support hwt hP hJ (Finset.univ.sup wt + 1) k hk ?_
  intro i j h
  have h1 := Finset.le_sup (f := wt) (Finset.mem_univ i)
  have h2 := Finset.le_sup (f := wt) (Finset.mem_univ j)
  omega
end GlobalTheory.CompanionTheory.Iwahori.Gauss
