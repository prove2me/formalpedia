-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.Red.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:33.899925+00:00
-- url     : https://prove2.me/submissions/e2874b08-3287-4277-968a-62b6d4211a14

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem

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
namespace GlobalTheory.CompanionTheory.HCdecomp
namespace Red
theorem _root_.solution {a a' : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) (h' : Red a') : Red (a + a') := by
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨u', hu', h'⟩ := h'
  refine ⟨u + u', Low.add _ _ hu hu', fun V _ _ E hE => ?_⟩
  have := (JJ E).add_mem (h V E hE) (h' V E hE)
  rw [map_add, map_add]
  convert this using 1; abel
end Red
end GlobalTheory.CompanionTheory.HCdecomp
