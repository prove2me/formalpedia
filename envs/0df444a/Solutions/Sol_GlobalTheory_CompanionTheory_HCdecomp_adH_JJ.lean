-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.adH_JJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:49:39.749556+00:00
-- url     : https://prove2.me/submissions/1093a7de-cbd8-489c-b822-871e94b3bb44

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_HH_NV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.HCdecomp
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) :
    JJ E ≤ (JJ E).comap (adH E) := by
  intro T hT x
  exact (NV E).sub_mem (HH_NV hE (hT x)) (hT _)
end GlobalTheory.CompanionTheory.HCdecomp
