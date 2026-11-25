-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.stWitt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:40.212535+00:00
-- url     : https://prove2.me/submissions/1ce20623-174a-4122-b559-88d869b96c59

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_frame_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}
namespace GlobalTheory.CompanionTheory.FlWitt
theorem _root_.solution : StWitt := by
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh l l' e f W e' f' W' F F'
  rcases le_total l l' with hl | hl
  · exact frame_core hs.1 hh hδ.1 hl F F'
  · obtain ⟨q, g, hg, ge, gf, hw⟩ := frame_core hs.1 hh hδ.1 hl F' F
    refine ⟨q.symm, g.symm, fun x y => ?_, fun i => ?_, fun i => ?_, fun w => ?_⟩
    · have := hg (g.symm x) (g.symm y)
      simpa using this.symm
    · rw [LinearEquiv.symm_apply_eq, ge, q.apply_symm_apply]
    · rw [LinearEquiv.symm_apply_eq, gf, q.apply_symm_apply]
    · simpa using (hw (g.symm w)).symm
end GlobalTheory.CompanionTheory.FlWitt
