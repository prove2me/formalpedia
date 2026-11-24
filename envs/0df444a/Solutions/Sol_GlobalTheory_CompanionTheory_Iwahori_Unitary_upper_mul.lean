-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.upper_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:27.618166+00:00
-- url     : https://prove2.me/submissions/c042f692-e5c1-4664-baee-bd544dbaf703

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_piece_mul_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.Unitary
variable {E ι : Type} [Ring E] [Fintype ι]
namespace GlobalTheory.CompanionTheory.Iwahori.Unitary
theorem _root_.solution {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) {x y : E}
    (hx : IsUpper wt P x) (hy : IsUpper wt P y) : IsUpper wt P (x * y) := by
  intro i j hij
  rw [piece_mul_mul hP]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge (wt k) (wt i) with h | h
  · rw [hx i k h, zero_mul]
  · rw [hy k j (lt_of_lt_of_le hij h), mul_zero]
end GlobalTheory.CompanionTheory.Iwahori.Unitary
