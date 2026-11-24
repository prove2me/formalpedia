-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.lowerUni_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:21.241991+00:00
-- url     : https://prove2.me/submissions/b3ad2969-e635-4b36-a844-6d1a13c3ce0c

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_lower_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_diag_mul

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
theorem _root_.solution {wt : ι → ℕ} {P : ι → E} (hP : IsPieces P) (hw : Function.Injective wt)
    {x y : E} (hx : IsLowerUni wt P x) (hy : IsLowerUni wt P y) : IsLowerUni wt P (x * y) :=
  ⟨lower_mul hP hx.1 hy.1, fun i => by
    rw [diag_mul hP hw hx.1 hy.1, hx.2, hy.2, hP.idem]⟩
end GlobalTheory.CompanionTheory.Iwahori.Unitary
