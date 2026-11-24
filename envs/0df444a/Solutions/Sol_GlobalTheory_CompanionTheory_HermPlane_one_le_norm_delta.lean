-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.one_le_norm_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:09.936506+00:00
-- url     : https://prove2.me/submissions/7561fcf0-9c4c-4ddf-a991-da761179d2f5

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) : 1 ≤ ‖δ‖ := by
  have := (hδ.2.1 1).1 (fun x hx => by
    rw [one_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ?_)
    rw [hs.2.1]
    exact hx)
  simpa using this
end GlobalTheory.CompanionTheory.HermPlane
