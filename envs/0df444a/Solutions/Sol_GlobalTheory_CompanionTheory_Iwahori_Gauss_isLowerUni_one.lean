-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.isLowerUni_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:25.430115+00:00
-- url     : https://prove2.me/submissions/1073f229-1aa6-463e-b845-a050e7c2cdaa

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
theorem _root_.solution (hP : IsPieces P) : IsLowerUni wt P 1 := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_one]
    exact hP.orth i j (fun e => by subst e; exact lt_irrefl _ h)
  · rw [mul_one, hP.idem]
end GlobalTheory.CompanionTheory.Iwahori.Gauss
