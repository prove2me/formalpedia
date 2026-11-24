-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.isUpper_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:26.299276+00:00
-- url     : https://prove2.me/submissions/541343d4-c0fe-4206-94d9-dad74961816d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Gauss_block_mul

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
theorem _root_.solution (hP : IsPieces P) {a b : E} (ha : IsUpper wt P a) (hb : IsUpper wt P b) :
    IsUpper wt P (a * b) := by
  intro i j hij
  rw [block_mul hP]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (wt l) (wt i) with h | h
  · rw [ha i l h, zero_mul]
  · rw [hb l j (lt_of_lt_of_le hij h), mul_zero]
end GlobalTheory.CompanionTheory.Iwahori.Gauss
