-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.UpInv.map_low_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:29.772882+00:00
-- url     : https://prove2.me/submissions/d82221c0-d1e9-4182-9453-d36b61f57895

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_UpperTriangularInverseIsUpper
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_UpInv_sum_pieces

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
theorem _root_.solution {wt : ι → ℕ} {P : ι → Module.End L V} (hP : IsPieces P)
    {a : Module.End L V} (ha : IsUpper wt P a) (m : ℕ) :
    (low wt P m).map a ≤ low wt P m := by
  rintro _ ⟨x, hx, rfl⟩ i hi
  have hx' : x ∈ low wt P m := hx
  rw [← sum_pieces hP x, map_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : m ≤ wt j
  · rw [hx' j hj, map_zero, map_zero]
  · have h := congrArg (fun T : Module.End L V => T x) (ha i j (by omega))
    simpa using h
end GlobalTheory.CompanionTheory.Iwahori.UpInv
