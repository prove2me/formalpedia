-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgSplit.latOf_isLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:12:08.436365+00:00
-- url     : https://prove2.me/submissions/7a552110-e244-4566-802d-683bd2315ed7

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
variable [IsUltrametricDist L]
namespace GlobalTheory.CompanionTheory.RgSplit
theorem _root_.solution {m : ℕ} (b : Module.Basis (Fin m) L V) : IsLat L (latOf b) :=
  ⟨m, b, fun _ => Iff.rfl⟩
end GlobalTheory.CompanionTheory.RgSplit
