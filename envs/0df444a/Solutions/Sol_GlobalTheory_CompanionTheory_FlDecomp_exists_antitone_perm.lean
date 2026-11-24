-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlDecomp.exists_antitone_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:23.906352+00:00
-- url     : https://prove2.me/submissions/46f8c66c-9029-486b-8d81-5f6044782259

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlDecomp
open CompanionTheory.Rg.FlB
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FlDecomp
theorem _root_.solution {n : ℕ} (m : Fin n → ℕ) : ∃ σ : Equiv.Perm (Fin n), Antitone (m ∘ σ) := by
  refine ⟨Tuple.sort (fun i => OrderDual.toDual (m i)), ?_⟩
  have := Tuple.monotone_sort (fun i => OrderDual.toDual (m i))
  intro i j hij
  exact this hij
end GlobalTheory.CompanionTheory.FlDecomp
