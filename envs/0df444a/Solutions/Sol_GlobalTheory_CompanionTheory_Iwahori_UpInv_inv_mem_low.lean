-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.UpInv.inv_mem_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:34.151839+00:00
-- url     : https://prove2.me/submissions/99036875-dff0-4349-9e80-8455288d6da7

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_map_low_eq

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
theorem _root_.solution [FiniteDimensional L V] {wt : ι → ℕ} {P : ι → Module.End L V}
    (hP : IsPieces P) {a a' : Module.End L V} (h1 : a * a' = 1) (h2 : a' * a = 1)
    (ha : IsUpper wt P a) {m : ℕ} {x : V} (hx : x ∈ low wt P m) : a' x ∈ low wt P m := by
  rw [← map_low_eq hP h1 h2 ha m] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h := congrArg (fun T : Module.End L V => T y) h2
  have h' : a' (a y) = y := by simpa using h
  rwa [h']
end GlobalTheory.CompanionTheory.Iwahori.UpInv
