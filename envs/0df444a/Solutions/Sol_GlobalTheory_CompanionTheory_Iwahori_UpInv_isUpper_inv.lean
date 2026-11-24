-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.UpInv.isUpper_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:49:12.982682+00:00
-- url     : https://prove2.me/submissions/c4743110-22f9-41c9-a975-0de31bed37ae

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_inv_mem_low
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_piece_mem_low

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.UpInv
variable {L V ι : Type} [Field L] [AddCommGroup V] [Module L V] [Fintype ι]
namespace GlobalTheory.CompanionTheory.Iwahori.UpInv
theorem _root_.solution : ∀ {L V ι : Type} [Field L] [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Fintype ι] (wt : ι → ℕ) (P : ι → Module.End L V),
    GlobalTheory.CompanionTheory.Iwahori.IsPieces P → ∀ a a' : Module.End L V, a * a' = 1 → a' * a = 1 →
      GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a → GlobalTheory.CompanionTheory.Iwahori.IsUpper wt P a' := by
  intro L V ι _ _ _ _ _ wt P hP a a' h1 h2 ha i j hij
  refine LinearMap.ext fun x => ?_
  have h := inv_mem_low hP h1 h2 ha (piece_mem_low (wt := wt) hP j x) i (by omega)
  simpa using h
end GlobalTheory.CompanionTheory.Iwahori.UpInv
