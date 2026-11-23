-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.eq_zero_of_mul_pieces
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:56.250674+00:00
-- url     : https://prove2.me/submissions/2617f1d1-c6e0-4228-8c2e-9dfae279f0a4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriUpperLowerFactorization

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
theorem _root_.solution (hP : IsPieces P) {y : E} (h : ∀ j, y * P j = 0) : y = 0 := by
  have : y * ∑ j, P j = 0 := by
    rw [Finset.mul_sum]; exact Finset.sum_eq_zero (fun j _ => h j)
  rwa [hP.sum, mul_one] at this
end GlobalTheory.CompanionTheory.Iwahori.Gauss
