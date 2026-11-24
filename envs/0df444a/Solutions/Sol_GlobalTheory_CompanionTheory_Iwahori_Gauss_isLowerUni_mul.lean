-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.isLowerUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:24.562895+00:00
-- url     : https://prove2.me/submissions/e5016ef7-fcea-4d4b-8448-7038796c775a

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
theorem _root_.solution (hwt : Function.Injective wt) (hP : IsPieces P) {a b : E}
    (ha : IsLowerUni wt P a) (hb : IsLowerUni wt P b) : IsLowerUni wt P (a * b) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [block_mul hP]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge (wt i) (wt l) with h | h
    · rw [ha.1 i l h, zero_mul]
    · rw [hb.1 l j (lt_of_le_of_lt h hij), mul_zero]
  · rw [block_mul hP, Finset.sum_eq_single i]
    · rw [ha.2, hb.2, hP.idem]
    · intro l _ hl
      rcases lt_trichotomy (wt i) (wt l) with h | h | h
      · rw [ha.1 i l h, zero_mul]
      · exact absurd (hwt h).symm hl
      · rw [hb.1 l i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
end GlobalTheory.CompanionTheory.Iwahori.Gauss
