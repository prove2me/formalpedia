-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.st_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:26.625138+00:00
-- url     : https://prove2.me/submissions/ac0408e6-4941-4e5b-b799-57edf39ac57f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_Unitary_st_block

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
variable {wt : ι → ℕ} {P : ι → E} {rev : ι → ι} {st : E → E}
namespace GlobalTheory.CompanionTheory.Iwahori.Unitary
theorem _root_.solution (hrev : ∀ i, rev (rev i) = i) (hord : ∀ i j, wt i < wt j → wt (rev j) < wt (rev i))
    (hmul : ∀ a b, st (a * b) = st b * st a) (h0 : st 0 = 0)
    (hst : ∀ i, st (P i) = P (rev i)) {x : E} (hx : IsUpper wt P x) : IsUpper wt P (st x) := by
  intro i j hij
  rw [st_block hrev hmul hst, hx (rev j) (rev i) (hord j i hij), h0]
end GlobalTheory.CompanionTheory.Iwahori.Unitary
