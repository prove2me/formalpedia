-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.Red.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:34.271775+00:00
-- url     : https://prove2.me/submissions/66b451a1-8e9c-4c70-be54-106d9287c833

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
theorem _root_.solution (c : ℂ) {a : FreeAlgebra ℂ (Fin n × Fin n)} (h : Red a) : Red (c • a) := by
  obtain ⟨u, hu, h⟩ := h
  refine ⟨c • u, Low.smul _ _ hu, fun V _ _ E hE => ?_⟩
  rw [map_smul, map_smul, ← smul_sub]
  exact (JJ E).smul_mem c (h V E hE)
end Red
end GlobalTheory.CompanionTheory.HCdecomp
