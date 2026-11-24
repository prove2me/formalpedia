-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.Gauss.sub_one_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:28.054165+00:00
-- url     : https://prove2.me/submissions/d1bbb627-fb8c-4ac9-b23c-f1deb62f231f

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
theorem _root_.solution {J : AddSubgroup E} (hJ : IsCongIdeal J P) {a b : E}
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) : a * b - 1 ∈ J := by
  have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
  rw [this]
  exact J.add_mem (J.add_mem (hJ.mul_mem _ ha _ hb) ha) hb
end GlobalTheory.CompanionTheory.Iwahori.Gauss
