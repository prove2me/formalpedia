-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Unitary.st_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:55.724517+00:00
-- url     : https://prove2.me/submissions/8c545e17-5539-42bb-9325-85ac00887e44

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntiInvolutionSwapsUpperLower

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
theorem _root_.solution (hrev : ∀ i, rev (rev i) = i) (hmul : ∀ a b, st (a * b) = st b * st a)
    (hst : ∀ i, st (P i) = P (rev i)) (x : E) (i j : ι) :
    P i * st x * P j = st (P (rev j) * x * P (rev i)) := by
  rw [hmul, hmul, hst, hst, hrev, hrev, mul_assoc]
end GlobalTheory.CompanionTheory.Iwahori.Unitary
